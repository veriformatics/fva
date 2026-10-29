import Proofs.Lifted
import FVA.Spec.CAbi
import FVA.Spec.Valid.Module

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec

/-- The shipped artifact has no imports, fixed 2 MiB memory, and exports decoder function 7
with the four-i32 to i32 signature. This is interface evidence, not R1–R3. -/
def artifactLayout : Prop :=
  Lifted.module.imports = [] ∧
  Lifted.module.mems = [{ min := 32, max := some 32 }] ∧
  Lifted.module.exports =
    [{ name := "memory", desc := .mem 0 },
     { name := "lz4_compress", desc := .func 6 },
     { name := "lz4_decompress", desc := .func 7 }] ∧
  Lifted.module.funcs[7]? = some Lifted.func7 ∧
  Lifted.module.types[4]? = some
    ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩ ∧
  Lifted.func7.type = 4

/-- The exact artifact satisfies FVA's WebAssembly module-validity judgment.
This proves Wasm typing and structural validity, not the buffer or LZ4 requirements. -/
def wasmValid : Prop := FVA.Wasm.Valid.ModuleValid Lifted.module

/-- For zero input length, the actual decoder code terminates, returns -1, and preserves
its entire store, for arbitrary pointers, capacity, memory, and host behavior. The explicit
function binding identifies the artifact's decoder in any store. Store preservation alone
is not an access-trace theorem and does not prove R1 for nonempty inputs. -/
def emptyInputPreservesStore : Prop :=
  ∀ (H : HostSem) (s : Store) (inst : ModuleInst) (src dst cap : BitVec 32),
    s.funcs[7]? = some (.wasm
      ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩ inst Lifted.func7) →
    Must H (fun
      | .returned s' vs => s' = s ∧ vs = [.i32 (-1)]
      | .trapped _ => False)
      (invokeConfig s 7 [.i32 src, .i32 dst, .i32 0, .i32 cap])

/-- One concrete input/output observation in a genuine fresh instance under every host.
Source is 131072 and destination is 1048576. This helper is not a universal LZ4 specification.
For errors the output observation can be empty, making no claim about partial writes. -/
def Replay (input : List UInt8) (cap : Nat) (result : BitVec 32)
    (output : List UInt8) : Prop :=
  ∀ H, ∃ s inst, Instance Lifted.module H s inst ∧
    Fits s 131072 input.length ∧ Fits s 1048576 cap ∧
    CallReturns H (s.withBytes 131072 input) inst "lz4_decompress"
      [.i32 131072, .i32 1048576, .i32 (BitVec.ofNat 32 input.length),
       .i32 (BitVec.ofNat 32 cap)]
      (fun s' vs => vs = [.i32 result] ∧ ∃ mem, s'.mems[0]? = some mem ∧
        (List.range output.length).map (fun k => mem.byte (1048576 + k)) = output)

/-- R2 example: valid empty-content block [0] succeeds in zero capacity. -/
def emptyBlock : Prop := Replay [0] 0 0 []

/-- R2 example: valid literal-only block decodes to ABCDE with exact capacity. -/
def literalBlock : Prop := Replay [80, 65, 66, 67, 68, 69] 5 5 [65, 66, 67, 68, 69]

/-- R2 example: independent valid block with offset 1 and an overlapping length-7 match,
followed by five final literals. Its last match begins 12 decoded bytes before the end. -/
def overlappingBlock : Prop :=
  Replay [19, 65, 1, 0, 80, 66, 67, 68, 69, 70] 13 13
    [65, 65, 65, 65, 65, 65, 65, 65, 66, 67, 68, 69, 70]

/-- R3 example: offset zero is rejected. This does not establish universal rejection. -/
def zeroOffset : Prop := Replay [16, 65, 0, 0, 80, 66, 67, 68, 69, 70] 13 (-1) []

/-- R3 example: offset 2 after only one decoded byte is rejected. -/
def excessiveOffset : Prop := Replay [16, 65, 2, 0, 80, 66, 67, 68, 69, 70] 13 (-1) []

/-- Capacity example: a valid five-literal block is rejected in capacity four. -/
def insufficientCapacity : Prop := Replay [80, 65, 66, 67, 68, 69] 4 (-1) []

/-- Malformed input example: unterminated literal-length extension is rejected. -/
def truncatedLength : Prop := Replay [240, 255] 64 (-1) []

end Proofs
