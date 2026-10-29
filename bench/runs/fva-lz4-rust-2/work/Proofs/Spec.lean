import Proofs.Lifted
import FVA.Spec.CAbi
import FVA.Spec.Valid.Module

/-! Partial verification claims, not the universal README requirements R1–R3.
The store contains the artifact's actual functions, types, exports and globals.
Memory is arbitrary, so these results do not depend on zero-filled caller buffers.
-/

namespace Proofs

open FVA.Wasm FVA.Wasm.Exec

/-- The artifact's allocation, with its stack-pointer global initialized. -/
noncomputable def allocation : Store × ModuleInst :=
  allocModule {} Lifted.module [] [.i32 65536] []

/-- The initialized artifact's code and dropped data segment, with caller-selected memory. -/
noncomputable def codeStore (mem : MemInst) : Store :=
  { allocation.1 with mems := [mem], datas := [{ data := [] }] }

/-- On zero input bytes the actual export returns -1 and leaves the entire store
unchanged, for every memory, source address, destination address and capacity.
This is a boundary case only; it does not establish R1–R3 in general. -/
def zero_input : Prop :=
  ∀ (H : HostSem) (mem : MemInst) (src dst cap : BitVec 32),
    CallReturns H (codeStore mem) allocation.2 "lz4_decompress"
      [.i32 src, .i32 dst, .i32 0, .i32 cap]
      (fun s vs => s = codeStore mem ∧ vs = [.i32 4294967295])

/-- The valid empty block [00], at address 131072, decodes into a zero-capacity
buffer at 131104, returns zero, and leaves the entire store unchanged.
Memory outside the input byte is arbitrary. This is one case of R2. -/
def empty_block : Prop :=
  ∀ (H : HostSem) (mem : MemInst), mem.pages = 32 → mem.byte 131072 = 0 →
    CallReturns H (codeStore mem) allocation.2 "lz4_decompress"
      [.i32 131072, .i32 131104, .i32 1, .i32 0]
      (fun s vs => s = codeStore mem ∧ vs = [.i32 0])

/-- Every one-byte literal payload in [10, b], at address 131072, decodes into
the one-byte buffer at 131104. The return is one, the output equals b, and every
other memory byte is unchanged. This is a restricted family of cases of R2/R3,
and checks final memory preservation outside the destination. It does not
state confinement of intermediate reads or writes. -/
def one_literal : Prop :=
  ∀ (H : HostSem) (mem : MemInst), mem.pages = 32 → mem.byte 131072 = 16 →
    CallReturns H (codeStore mem) allocation.2 "lz4_decompress"
      [.i32 131072, .i32 131104, .i32 2, .i32 1]
      (fun s vs => vs = [.i32 1] ∧ ∃ out,
        s.mems[0]? = some out ∧ out.byte 131104 = mem.byte 131073 ∧
        ∀ a, a ≠ 131104 → out.byte a = mem.byte a)

/-- The malformed block [00, 00, 00] has a forbidden zero match offset.
The export returns -1 without changing the store, with output capacity four.
This checks one invalid-input case relevant to R3, not its converse in general. -/
def zero_offset : Prop :=
  ∀ (H : HostSem) (mem : MemInst), mem.pages = 32 →
    mem.byte 131072 = 0 → mem.byte 131073 = 0 → mem.byte 131074 = 0 →
    CallReturns H (codeStore mem) allocation.2 "lz4_decompress"
      [.i32 131072, .i32 131104, .i32 3, .i32 4]
      (fun s vs => s = codeStore mem ∧ vs = [.i32 4294967295])

/-- The shipped module satisfies FVA's WebAssembly module typing rules.
This is not a proof of buffer confinement or of the LZ4 requirements. -/
def module_valid : Prop := FVA.Wasm.Valid.ModuleValid Lifted.module

/-- For every host semantics, some 32-page memory makes codeStore exactly a
successfully initialized fresh instance of the shipped artifact. -/
def fresh_runtime_store : Prop :=
  ∀ H, ∃ mem : MemInst, mem.pages = 32 ∧
    Instance Lifted.module H (codeStore mem) allocation.2

/-- The shipped module successfully instantiates under every host semantics.
This establishes existence only, not the universal decoding requirements. -/
def initializable : Prop := Instantiable Lifted.module

end Proofs
