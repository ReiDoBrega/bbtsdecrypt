package main

//go:generate goversioninfo -icon=icon.ico
import (
	"crypto/aes"
	"crypto/cipher"
	"flag"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"time"
)

const (
	TS_PKT      = 188
	SYNC        = 0x47
	PID_PAT     = 0x0000
	PID_SDT     = 0x0011
	PID_PMT     = 0x1000
	VIDEO_PID   = 0x0100
	AUDIO_PID   = 0x0101
	IV_COPY_LEN = 12
)

// ANSI color codes
const (
	ColorGreen = "\033[32m"
	ColorReset = "\033[0m"
	ColorBold  = "\033[1m"
)

// Progress bar
type Progress struct {
	total        int64
	width        int
	minIntervalS float64
	lastT        time.Time
	lastDone     int64
	startTime    time.Time
	quiet        bool
	mu           sync.Mutex
}

func NewProgress(total int64, quiet bool) *Progress {
	return &Progress{
		total:        total,
		width:        30,
		minIntervalS: 0.05,
		lastT:        time.Now(),
		lastDone:     -1,
		startTime:    time.Now(),
		quiet:        quiet,
	}
}

func (p *Progress) Update(done int64) {
	if p.quiet {
		return
	}

	p.mu.Lock()
	defer p.mu.Unlock()

	now := time.Now()
	if done == p.lastDone {
		return
	}
	if now.Sub(p.lastT).Seconds() < p.minIntervalS && done < p.total {
		return
	}

	p.lastT = now
	p.lastDone = done

	pct := float64(done) / float64(p.total) * 100.0
	filled := int(int64(p.width) * done / p.total)

	filledBar := ColorGreen + strings.Repeat("█", filled) + ColorReset
	emptyBar := strings.Repeat("░", p.width-filled)

	elapsed := now.Sub(p.startTime).Seconds()
	var etaStr string
	if done > 0 && elapsed > 0 {
		rate := float64(done) / elapsed
		remaining := float64(p.total - done)
		eta := remaining / rate

		etaMin := int(eta) / 60
		etaSec := int(eta) % 60
		etaStr = fmt.Sprintf("ETA: %02d:%02d", etaMin, etaSec)
	} else {
		etaStr = "ETA: --:--"
	}

	fmt.Printf("\r%s%s %6.2f%% | %s", filledBar, emptyBar, pct, etaStr)
}

func (p *Progress) Finish() {
	if p.quiet {
		return
	}
	fmt.Printf("\r%s%s%s 100.00%%\n", ColorGreen, strings.Repeat("█", p.width), ColorReset)
}

// Helpers
func hexToBytes(hexStr string, nLen int) ([]byte, error) {
	s := strings.TrimSpace(hexStr)
	if strings.HasPrefix(s, "0x") || strings.HasPrefix(s, "0X") {
		s = s[2:]
	}
	if len(s) != nLen*2 {
		return nil, fmt.Errorf("invalid hex length. Expected %d hex chars, got %d", nLen*2, len(s))
	}

	result := make([]byte, nLen)
	for i := 0; i < nLen; i++ {
		_, err := fmt.Sscanf(s[i*2:(i+1)*2], "%02x", &result[i])
		if err != nil {
			return nil, err
		}
	}
	return result, nil
}

func ctrInc(counter []byte) {
	c := 1
	for i := 15; i >= 0; i-- {
		c += int(counter[i])
		counter[i] = byte(c & 0xFF)
		c >>= 8
		if c == 0 {
			break
		}
	}
}

func tsPID(pkt []byte) uint16 {
	return uint16((uint16(pkt[1]&0x1F) << 8) | uint16(pkt[2]))
}

func tsPUSI(pkt []byte) bool {
	return (pkt[1] & 0x40) != 0
}

func tsAFC(pkt []byte) int {
	return int((pkt[3] >> 4) & 0x3)
}

func tsHasPayload(pkt []byte) bool {
	afc := tsAFC(pkt)
	return afc == 1 || afc == 3
}

func tsPayloadOffset(pkt []byte) int {
	afc := tsAFC(pkt)
	switch afc {
	case 1:
		return 4
	case 3:
		alen := int(pkt[4])
		return 5 + alen
	default:
		return TS_PKT
	}
}

func outputTSPath(outArg string) string {
	ext := filepath.Ext(outArg)
	if ext != "" {
		return outArg
	}
	return outArg + ".ts"
}

// PSI Assembler
type PSIAssembler struct {
	buf           []byte
	expectedTotal *int
	collecting    bool
	mu            sync.Mutex
}

func NewPSIAssembler() *PSIAssembler {
	return &PSIAssembler{
		buf: make([]byte, 0),
	}
}

func (pa *PSIAssembler) Push(pkt []byte) []byte {
	pa.mu.Lock()
	defer pa.mu.Unlock()

	if len(pkt) != TS_PKT || !tsHasPayload(pkt) {
		return nil
	}

	off := tsPayloadOffset(pkt)
	if off >= TS_PKT {
		return nil
	}

	payload := pkt[off:]

	if tsPUSI(pkt) {
		pointer := int(payload[0])
		payload = payload[1:]
		if pointer > len(payload) {
			return nil
		}
		payload = payload[pointer:]
		pa.buf = make([]byte, 0)
		pa.expectedTotal = nil
		pa.collecting = true
	}

	if !pa.collecting {
		return nil
	}

	pa.buf = append(pa.buf, payload...)

	if pa.expectedTotal == nil && len(pa.buf) >= 3 {
		sectionLength := int((uint16(pa.buf[1]&0x0F) << 8) | uint16(pa.buf[2]))
		expected := 3 + sectionLength
		pa.expectedTotal = &expected
	}

	if pa.expectedTotal != nil && len(pa.buf) >= *pa.expectedTotal {
		section := make([]byte, *pa.expectedTotal)
		copy(section, pa.buf[:*pa.expectedTotal])
		pa.buf = make([]byte, 0)
		pa.expectedTotal = nil
		pa.collecting = false
		return section
	}

	return nil
}

// Parse SDT and extract IV
func parseSDTAndSetIV(section []byte, ivec []byte) bool {
	if len(section) < 16 || section[0] != 0x42 {
		return false
	}

	sectionLength := int((uint16(section[1]&0x0F) << 8) | uint16(section[2]))
	end := 3 + sectionLength
	if end > len(section) {
		return false
	}

	pos := 3 + 8
	for pos+5 <= end-4 {
		descLoopLen := int((uint16(section[pos+3]&0x0F) << 8) | uint16(section[pos+4]))
		dpos := pos + 5
		dend := dpos + descLoopLen

		for dpos+2 <= dend && dpos+2 <= end-4 {
			tag := section[dpos]
			length := int(section[dpos+1])
			dpos += 2
			if dpos+length > len(section) {
				break
			}
			body := section[dpos : dpos+length]
			dpos += length

			if tag == 0x48 && len(body) >= 3 {
				providerLen := int(body[1])
				if 2+providerLen >= len(body) {
					continue
				}

				snLenIdx := 2 + providerLen
				snLen := int(body[snLenIdx])
				serviceName := string(body[snLenIdx+1 : snLenIdx+1+snLen])

				if !strings.Contains(serviceName, "mdcm|") {
					continue
				}

				parts := strings.Split(serviceName, "|")
				if len(parts) < 4 {
					continue
				}

				ivHex := parts[3]
				if ivHex == "" {
					continue
				}
				ivHex = ivHex[1:]

				ivBin, err := hexToBytes(ivHex, 16)
				if err != nil {
					continue
				}

				for i := 0; i < 16; i++ {
					ivec[i] = 0
				}
				for i := 0; i < IV_COPY_LEN && i < len(ivBin); i++ {
					ivec[i] = ivBin[i]
				}
				return true
			}
		}

		pos = dend
	}

	return false
}

// Parse PMT streams
type StreamInfo struct {
	PID        uint16
	StreamType byte
}

func parsePMTStreams(section []byte) []StreamInfo {
	if len(section) < 12 || section[0] != 0x02 {
		return nil
	}

	sectionLength := int((uint16(section[1]&0x0F) << 8) | uint16(section[2]))
	end := 3 + sectionLength
	if end > len(section) {
		return nil
	}

	programInfoLen := int((uint16(section[10]&0x0F) << 8) | uint16(section[11]))
	pos := 12 + programInfoLen

	var out []StreamInfo
	for pos+5 <= end-4 {
		st := section[pos]
		pid := uint16((uint16(section[pos+1]&0x1F) << 8) | uint16(section[pos+2]))
		esInfoLen := int((uint16(section[pos+3]&0x0F) << 8) | uint16(section[pos+4]))
		out = append(out, StreamInfo{PID: pid, StreamType: st})
		pos += 5 + esInfoLen
	}

	return out
}

func findStreamType(streams []StreamInfo, pid uint16) byte {
	for _, s := range streams {
		if s.PID == pid {
			return s.StreamType
		}
	}
	return 0
}

type EncState struct {
	aesECBUser cipher.Block
	// ivec holds the BASE IV for the current segment (from SDT).
	// It must NOT be mutated during decryption — a copy is made per-PES.
	ivec  []byte
	ready bool
	mu    sync.Mutex
}

// PES Header Chunk
type PESHeaderChunk struct {
	headerBytes []byte
	headerSize  int
}

// decryptESSparseWithEmulationRemoval decrypts the Elementary Stream bytes in-place.
// It receives a COPY of the base IV (ivStart) so it never mutates the state IV.
func decryptESSparseWithEmulationRemoval(es []byte, block cipher.Block, ivStart []byte) {
	// Remove emulation prevention bytes (0x00 0x00 0x03 → 0x00 0x00)
	newES := make([]byte, 0, len(es))
	i := 0
	for i < len(es) {
		if i+2 < len(es) && es[i] == 0 && es[i+1] == 0 && es[i+2] == 3 {
			newES = append(newES, 0, 0)
			i += 3
		} else {
			newES = append(newES, es[i])
			i++
		}
	}

	// Work on a local counter copy so the caller's IV is never touched
	iv := make([]byte, 16)
	copy(iv, ivStart)

	esLen := len(newES)
	pos := 0
	counter := 0

	for esLen > 0 {
		ctrInc(iv)
		tmp := make([]byte, 16)
		copy(tmp, iv)

		if esLen <= 16 || counter%10 == 0 {
			block.Encrypt(tmp, tmp)
		}

		decLen := 16
		if esLen < 16 {
			decLen = esLen
		}

		for k := 0; k < decLen; k++ {
			newES[pos+k] ^= tmp[k]
		}

		esLen -= decLen
		pos += 16
		counter++
	}

	// Re-insert emulation prevention bytes if sizes differ - FIX
	if len(newES) != len(es) {
		diff := len(es) - len(newES)
		if diff > 0 {
			newES = append(newES, es[len(es)-diff:]...)
		}
	}
	copy(es, newES)
}

// decryptPESNormal decrypts a full PES packet in-place using a snapshot of the
// current segment IV.  The snapshot is taken once per call so that processing
// multiple PES units within the same segment all start from the same base IV,
// exactly as they would when each .bbts file is decrypted independently.
func decryptPESNormal(pes []byte, streamType byte, block cipher.Block, ivSnap []byte) {
	if len(pes) < 9 {
		return
	}

	pesHeaderLen := int(pes[8])
	headerEnd := 9 + pesHeaderLen
	if headerEnd > len(pes) {
		return
	}

	newPES := make([]byte, 0, len(pes))
	newPES = append(newPES, pes[:headerEnd]...)

	nalHdrLen := 1
	if streamType != 0x1B {
		nalHdrLen = 2
	}

	posSt := headerEnd
	i := posSt

	for i < len(pes) {
		if i == len(pes)-1 {
			if len(pes)-2 > posSt+3+nalHdrLen {
				newPES = append(newPES, pes[posSt:posSt+3+nalHdrLen]...)
				es := pes[posSt+3+nalHdrLen : len(pes)-2]
				esCopy := make([]byte, len(es))
				copy(esCopy, es)
				if len(esCopy) > 0 {
					decryptESSparseWithEmulationRemoval(esCopy, block, ivSnap)
				}
				newPES = append(newPES, esCopy...)
				newPES = append(newPES, pes[len(pes)-2:]...)
			} else {
				newPES = append(newPES, pes[posSt:]...)
			}
		} else {
			if i+2 < len(pes) && pes[i] == 0 && pes[i+1] == 0 && pes[i+2] == 1 {
				if i != posSt {
					if i-2 > posSt+3+nalHdrLen {
						newPES = append(newPES, pes[posSt:posSt+3+nalHdrLen]...)

						es := make([]byte, 0)
						flag := false
						if pes[i-1] == 0 {
							flag = true
							es = append(es, pes[posSt+3+nalHdrLen:i-3]...)
						} else {
							es = append(es, pes[posSt+3+nalHdrLen:i-2]...)
						}

						if len(es) > 0 {
							decryptESSparseWithEmulationRemoval(es, block, ivSnap)
						}
						newPES = append(newPES, es...)

						if flag {
							newPES = append(newPES, pes[i-3:i]...)
						} else {
							newPES = append(newPES, pes[i-2:i]...)
						}
					} else {
						newPES = append(newPES, pes[posSt:i]...)
					}
					posSt = i
				}
			}
		}
		i++
	}

	copy(pes, newPES)
}

func decryptBBTSToTSFile(bbtsPath, outTSPath, userKeyHex string, noAudio, noVideo bool, prog *Progress) error {
	userKey, err := hexToBytes(userKeyHex, 16)
	if err != nil {
		return err
	}

	aesBlock, err := aes.NewCipher(userKey)
	if err != nil {
		return err
	}

	state := &EncState{
		aesECBUser: aesBlock,
		ivec:       make([]byte, 16),
		ready:      false,
	}

	var pmtStreams []StreamInfo
	sdtAsm := NewPSIAssembler()
	pmtAsm := NewPSIAssembler()

	var pes []byte
	var pesHeaders []PESHeaderChunk
	lastPID := uint16(0xFFFF)

	// ivSnapForPES holds a frozen copy of the IV at the moment the PES started.
	// Each new PES unit captures the current segment IV so that decryption is
	// independent and deterministic regardless of how many PES units came before.
	var ivSnapForPES []byte

	fin, err := os.Open(bbtsPath)
	if err != nil {
		return err
	}
	defer fin.Close()

	fout, err := os.Create(outTSPath)
	if err != nil {
		return err
	}
	defer fout.Close()

	flushPES := func() error {
		if len(pes) == 0 || len(pesHeaders) == 0 || !state.ready {
			pes = nil
			pesHeaders = nil
			ivSnapForPES = nil
			lastPID = 0xFFFF
			return nil
		}

		sidPrev := byte(0xE1)
		if len(pes) > 3 {
			sidPrev = pes[3]
		}

		if sidPrev == 0xE0 && len(pes) > 8 && ivSnapForPES != nil {
			streamType := findStreamType(pmtStreams, lastPID)
			decryptPESNormal(pes, streamType, state.aesECBUser, ivSnapForPES)
		}

		// Reconstruct TS packets preserving the EXACT original packet layout.
		// Each header chunk knows precisely how many payload bytes it carried,
		// so we copy exactly that many bytes from the PES buffer — no more, no
		// less.  This prevents DTS/PTS corruption caused by size miscalculation.
		pesRemain := len(pes)
		pesPos := 0
		for i, h := range pesHeaders {
			// Payload capacity = 188 - header_size, but the last packet of the
			// PES may have had stuffing bytes already embedded in the original
			// adaptation field.  We MUST write exactly 188 bytes per packet.
			payloadCap := TS_PKT - h.headerSize

			var payload []byte
			if pesRemain <= 0 {
				// No more PES data; fill with stuffing (0xFF) :D
				payload = make([]byte, payloadCap)
				for k := range payload {
					payload[k] = 0xFF
				}
			} else if pesRemain < payloadCap {
				// Last packet: not enough data to fill the slot.
				// We must pad to keep the TS packet exactly 188 bytes.
				// Only valid for the last header chunk.
				if i == len(pesHeaders)-1 {
					// Insert stuffing via adaptation field in the header copy.
					hdr := make([]byte, h.headerSize)
					copy(hdr, h.headerBytes)

					stuffingNeeded := payloadCap - pesRemain

					afc := int((hdr[3] >> 4) & 0x3)
					if afc == 1 {
						// No adaptation field yet — switch to AFC=3 and add one
						hdr[3] = (hdr[3] & 0x0F) | 0x30 // set AFC bits to 3
						if stuffingNeeded == 1 {
							// Minimal: 1 byte adaptation field length = 0
							// Shift payload start by 1 → need to prepend 1 byte
							hdr = append(hdr, 0x00) // adaptation_field_length = 0
						} else {
							// adaptation_field_length = stuffingNeeded-1,
							// then (stuffingNeeded-2) stuffing bytes (0xFF)
							// after 1 flag byte (0x00)
							hdr = append(hdr, byte(stuffingNeeded-1))
							hdr = append(hdr, 0x00) // flags byte
							for s := 0; s < stuffingNeeded-2; s++ {
								hdr = append(hdr, 0xFF)
							}
						}
					} else if afc == 3 {
						// Already has an adaptation field — extend it
						afLen := int(hdr[4])
						extra := stuffingNeeded
						hdr[4] = byte(afLen + extra)
						// Insert stuffing bytes right after the existing AF
						newHdr := make([]byte, 0, len(hdr)+extra)
						newHdr = append(newHdr, hdr[:5+afLen]...)
						for s := 0; s < extra; s++ {
							newHdr = append(newHdr, 0xFF)
						}
						newHdr = append(newHdr, hdr[5+afLen:]...)
						hdr = newHdr
					}

					fout.Write(hdr)
					fout.Write(pes[pesPos : pesPos+pesRemain])
					pesPos += pesRemain
					pesRemain = 0
					continue
				}
				// Not last packet and we ran out of data — write what we have
				payload = pes[pesPos : pesPos+pesRemain]
				pesPos += pesRemain
				pesRemain = 0
			} else {
				payload = pes[pesPos : pesPos+payloadCap]
				pesPos += payloadCap
				pesRemain -= payloadCap
			}

			fout.Write(h.headerBytes)
			fout.Write(payload)
		}

		pes = nil
		pesHeaders = nil
		ivSnapForPES = nil
		lastPID = 0xFFFF
		return nil
	}

	buf := make([]byte, TS_PKT)
	done := int64(0)

	for {
		_, err := io.ReadFull(fin, buf)
		if err == io.EOF || err == io.ErrUnexpectedEOF {
			flushPES()
			break
		}
		if err != nil {
			return err
		}

		pkt := make([]byte, TS_PKT)
		copy(pkt, buf)
		done += int64(TS_PKT)
		if prog != nil {
			prog.Update(done)
		}

		if pkt[0] != SYNC {
			fout.Write(pkt)
			continue
		}

		pid := tsPID(pkt)

		if pid == PID_PAT {
			flushPES()
			fout.Write(pkt)
			continue
		}

		if pid == PID_SDT {
			flushPES()

			sec := sdtAsm.Push(pkt)
			if sec != nil {
				newIVec := make([]byte, 16)
				if parseSDTAndSetIV(sec, newIVec) {
					// Only update if the IV actually changed (new segment)
					if !ivEqual(state.ivec, newIVec) {
						copy(state.ivec, newIVec)
						pmtStreams = nil
					}
					state.ready = true
				}
			}
			fout.Write(pkt)
			continue
		}

		if pid == PID_PMT {
			flushPES()
			sec := pmtAsm.Push(pkt)
			if sec != nil && state.ready {
				pmtStreams = parsePMTStreams(sec)
			}
			fout.Write(pkt)
			continue
		}

		if !state.ready {
			if noAudio && pid == AUDIO_PID {
				continue
			}
			if noVideo && pid == VIDEO_PID {
				continue
			}
			fout.Write(pkt)
			continue
		}

		if noAudio && pid == AUDIO_PID {
			flushPES()
			continue
		}

		if noVideo && pid == VIDEO_PID {
			flushPES()
			continue
		}

		interceptPIDs := map[uint16]bool{}
		if !noVideo {
			interceptPIDs[VIDEO_PID] = true
		}
		if !noAudio {
			interceptPIDs[AUDIO_PID] = true
		}

		if !interceptPIDs[pid] {
			flushPES()
			fout.Write(pkt)
			continue
		}

		if !tsHasPayload(pkt) {
			flushPES()
			fout.Write(pkt)
			continue
		}

		off := tsPayloadOffset(pkt)
		if off >= TS_PKT {
			flushPES()
			fout.Write(pkt)
			continue
		}

		isNewPES := false
		if off+8 < TS_PKT && pkt[off] == 0x00 && pkt[off+1] == 0x00 && pkt[off+2] == 0x01 {
			sid := pkt[off+3]
			if sid == 0xC0 || sid == 0xE0 {
				isNewPES = true
			}
		}

		if isNewPES && len(pes) > 0 {
			flushPES()
		}

		if !isNewPES && len(pes) == 0 {
			fout.Write(pkt)
			continue
		}

		if isNewPES {
			ivSnapForPES = make([]byte, 16)
			copy(ivSnapForPES, state.ivec)
		}

		if tsAFC(pkt) == 3 {
			pes = append(pes, pkt[off:]...)
			pesHeaders = append(pesHeaders, PESHeaderChunk{
				headerBytes: append([]byte{}, pkt[:off]...),
				headerSize:  off,
			})
		} else {
			pes = append(pes, pkt[4:]...)
			pesHeaders = append(pesHeaders, PESHeaderChunk{
				headerBytes: append([]byte{}, pkt[:4]...),
				headerSize:  4,
			})
		}

		lastPID = pid
	}

	return nil
}

func ivEqual(a, b []byte) bool {
	if len(a) != 16 || len(b) != 16 {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

func printHelp() {
	fmt.Printf("%sBBTSDecrypt - Version 1.6%s\n", ColorBold, ColorReset)
	fmt.Println("(c) 2025-2026 @duck @ReiDoBrega")
	fmt.Printf("usage: %s [options] <input.bbts> <output>\n\n", filepath.Base(os.Args[0]))
	fmt.Println("Options are:")
	fmt.Println("  --show-progress : show progress details during decryption")
	fmt.Println("  --key <key>")
	fmt.Println("       <key> is a 128-bit AES key in hex (32 characters)")
	fmt.Println("  --no-audio : remove audio from output (video only)")
	fmt.Println("  --no-video : remove video from output (audio only)")
	fmt.Println("  --help : show this help message")
}

// Main
func main() {
	userKey := flag.String("key", "", "User AES key (32 hex characters)")
	noAudio := flag.Bool("no-audio", false, "Remove audio from output")
	noVideo := flag.Bool("no-video", false, "Remove video from output")
	showProgress := flag.Bool("show-progress", false, "Show progress bar during decryption")
	help := flag.Bool("help", false, "Show help message")

	flag.Parse()

	if *help {
		printHelp()
		os.Exit(0)
	}

	args := flag.Args()

	if *userKey == "" || len(args) < 2 {
		printHelp()
		os.Exit(1)
	}

	inputPath := args[0]
	outputPath := args[1]

	if *noAudio && *noVideo {
		fmt.Fprintf(os.Stderr, "ERROR: Cannot use --no-audio and --no-video together (no streams would remain)\n")
		os.Exit(1)
	}

	_, err := hexToBytes(*userKey, 16)
	if err != nil {
		fmt.Fprintf(os.Stderr, "ERROR: Invalid key: %v\n", err)
		os.Exit(1)
	}

	fileInfo, err := os.Stat(inputPath)
	if err != nil {
		fmt.Fprintf(os.Stderr, "ERROR: %v\n", err)
		os.Exit(1)
	}

	quiet := !*showProgress
	prog := NewProgress(fileInfo.Size(), quiet)
	outTS := outputTSPath(outputPath)

	err = decryptBBTSToTSFile(inputPath, outTS, *userKey, *noAudio, *noVideo, prog)
	if err != nil {
		fmt.Fprintf(os.Stderr, "\nERROR: %v\n", err)
		os.Exit(1)
	}

	prog.Finish()
}
