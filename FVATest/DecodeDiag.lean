import FVA.Impl.Decode.Module

/-!
# Decoder rejection verdicts (U28a mutation survivors, classifier-1)

The decoder's theorems (`decode_sound`/`decode_complete`, T1–T3) cover successful decodes alone.
Its rejections are specified too: each `unsupported` verdict names its `FVA.Profile.Excluded`
class (U28a I1, line 8) and every failure carries the bytes left at its point (U2 I1). These
checks pin the verdicts the survivors of U28a's mutation update changed: a class, a bytes-left
count. The module sits in `FVATest.Certs`' import closure: that proof root is built for every
decoder mutant (`FVATest/Mutate/config.json`), and outside the test executables' closures, so
adding it re-keys survivors alone (`docs/contracts/U12-mutation.md` R2).
-/

namespace FVA.Test.DecodeDiag

open FVA.Wasm FVA.Wasm.Decode

-- control: a supported abstract heap type decodes
example : heapType 0x70 1 = .ok (.abs .func) 0 0 := rfl

-- excluded heap types name their class (`absHeapExcluded`); bytes left at the type byte
example : (heapType 0x6A 1 : Res HeapType) = .unsup 1 "gc-types: heap type" := rfl
example : (heapType 0x71 1 : Res HeapType) = .unsup 1 "gc-types: heap type" := rfl
example : (heapType 0x72 1 : Res HeapType) = .unsup 1 "bottom-types: heap type" := rfl

-- malformed heap, value and block types: bytes left at the failing byte, `0` at an end
example : (heapType 0 0 : Res HeapType) = .bad 0 "unexpected end" := rfl
example : (heapType 0x75 1 : Res HeapType) = .bad 1 "malformed heap type" := rfl
example : (valType 0 0 : Res ValType) = .bad 0 "unexpected end" := rfl
example : (valType 0x00 1 : Res ValType) = .bad 1 "malformed value type" := rfl
example : (blockType 0 0 : Res BlockType) = .bad 0 "unexpected end" := rfl
example : (blockType 0x75 1 : Res BlockType) = .bad 1 "malformed block type" := rfl

-- `v128` in a block type: SIMD, not a negative type index (`valTypeStart`)
example : (blockType 0x7B 1 : Res BlockType) = .unsup 1 "simd: v128 value type" := rfl

-- legacy exception handling + GC + SIMD opcodes name their classes (bytes left at the opcode)
example : (lowInstr 0x07 0 0 1 : Res Instr) = .unsup 1 "legacy-exceptions: try, catch or rethrow" :=
  rfl
example : (lowInstr 0x09 0 0 1 : Res Instr) = .unsup 1 "legacy-exceptions: try, catch or rethrow" :=
  rfl
example : (lowInstr 0x18 0 0 1 : Res Instr) = .unsup 1 "legacy-exceptions: delegate or catch_all" :=
  rfl
example : (lowInstr 0x19 0 0 1 : Res Instr) = .unsup 1 "legacy-exceptions: delegate or catch_all" :=
  rfl
example : (highInstr 0xD3 0 0 1 : Res Instr) = .unsup 1 "gc-instructions: ref.eq" := rfl
example : (highInstr 0xFD 0 0 1 : Res Instr) = .unsup 1 "simd: 0xFD prefix" := rfl

-- limits flag 5 = 64-bit limits with a maximum (memory64), not shared limits
example : (limits 0x000005 3 : Res Limits) = .unsup 3 "memory64: 64-bit limits" := rfl

-- `0x4F` with no supertypes over an array (`0x5E`) or struct (`0x5F`) composite type: GC
example : (subType 0x00785E004F 5 : Res FuncType) = .unsup 3 "gc-types: struct or array type" :=
  rfl
example : (subType 0x005F004F 4 : Res FuncType) = .unsup 2 "gc-types: struct or array type" := rfl

-- empty input: bytes left 0
example : (recType 0 0 : Res RecType) = .bad 0 "unexpected end" := rfl
example : (table 0 0 : Res Table) = .bad 0 "unexpected end" := rfl

end FVA.Test.DecodeDiag
