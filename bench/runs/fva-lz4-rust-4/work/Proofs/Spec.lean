import FVA.Spec.CAbi
import Proofs.Lifted

namespace Proofs

open FVA.Wasm FVA.Wasm.Exec

/-- The decoded artifact's decoder export, function body, and fixed memory layout. -/
def artifactProfile : Prop :=
  Lifted.module.imports = [] ∧ Lifted.module.start = none ∧
  Lifted.module.mems = [⟨32, some 32⟩] ∧
  Lifted.module.exports[2]? = some ⟨"lz4_decompress", .func 7⟩ ∧
  Lifted.module.funcs[7]? = some Lifted.func7 ∧ Lifted.func7.type = 4 ∧
  Lifted.module.types[4]? = some
    ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩

/-- The artifact has a successfully initialized fresh instance under every host semantics. -/
def artifactInitializes : Prop := Instantiable Lifted.module

/-- The shipped decoder's zero-input-length branch always terminates, returns -1, and
leaves the entire store unchanged. This holds for arbitrary argument bits and any store
containing the decoded function at address 7; it does not require buffer preconditions. -/
def zeroLengthRejected : Prop :=
  ∀ (H : HostSem) (s : Store) (inst : ModuleInst) (src dst cap : BitVec 32),
    s.funcs[7]? = some (.wasm
      ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩ inst Lifted.func7) →
    Must H (fun o => o = .returned s [.i32 4294967295])
      (invokeConfig s 7 [.i32 src, .i32 dst, .i32 0, .i32 cap])

/-- The valid empty block (a single zero byte) decodes to zero bytes with cap = 0,
without modifying the store, at every readable source address. The hypotheses describe
the decoder function and memory in the call state; instantiation is not asserted here. -/
def emptyBlockDecoded : Prop :=
  ∀ (H : HostSem) (s : Store) (inst : ModuleInst) (src dst : BitVec 32) (mem : MemInst),
    s.funcs[7]? = some (.wasm
      ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩ inst Lifted.func7) →
    inst.mems = [0] → s.mems[0]? = some mem →
    src.toNat + 1 ≤ mem.size → mem.byte src.toNat = 0 →
    Must H (fun o => o = .returned s [.i32 0])
      (invokeConfig s 7 [.i32 src, .i32 dst, .i32 1, .i32 0])

end Proofs
