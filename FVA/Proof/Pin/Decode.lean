import FVA.Impl.Decode.Module

/-!
# Decoder error coordinates, pinned

U2 I1: "failures carry bytes-left, rebased at each sub-input, file offset = `len − rem`".
Soundness and completeness fix the `.ok` results alone, so these concrete failures pin the
coordinates (U12 survivors: reviewer-8 F1).
-/

namespace FVA.Wasm.Decode.Pin

theorem decode_magic : decode 0 8 = .error (.malformed 0 "magic header not detected") := rfl

theorem decode_version :
    decode 0x000000026d736100 8 = .error (.malformed 4 "unknown binary version") := rfl

theorem decode_tag_section :
    decode 0x0d000000016d736100 9 =
      .error (.unsupported 8 "exception handling (tag section)") := rfl

theorem byte_end : byte 0 0 = .bad 0 "unexpected end" := rfl

theorem uleb_end : uleb 1 32 0 0 = .bad 0 "unexpected end" := rfl

theorem sleb_end : sleb 1 32 0 0 = .bad 0 "unexpected end" := rfl

theorem seq_end : seq 2 [] 0x0041 2 = .bad 0 "unexpected end" := rfl

theorem sub_short : sub 3 (leNat 1) 0 5 = .bad 4 "section size mismatch" := rfl

theorem sub_overrun : sub 3 (leNat 4) 0 5 = .bad 5 "unexpected end" := rfl

theorem sub_unsup : sub 3 valType 0x7b 5 = .unsup 5 "v128 (SIMD)" := rfl

theorem utf8_continuation : utf8 1 0x80 1 = .bad 1 "malformed UTF-8 encoding" := rfl

theorem utf8_two : utf8 1 0xc2 1 = .bad 1 "malformed UTF-8 encoding" := rfl

theorem utf8_three : utf8 1 0xe0 1 = .bad 1 "malformed UTF-8 encoding" := rfl

theorem utf8_four : utf8 1 0xf0 1 = .bad 1 "malformed UTF-8 encoding" := rfl

theorem utf8_invalid : utf8 1 0xf5 1 = .bad 1 "malformed UTF-8 encoding" := rfl

end FVA.Wasm.Decode.Pin
