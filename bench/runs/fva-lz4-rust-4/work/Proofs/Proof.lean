import Proofs.Spec
import Proofs.Init
import FVA.Proof.Lib

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Proofs

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

theorem artifactProfile_holds : artifactProfile := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem zeroLengthRejected_holds : zeroLengthRejected := by
  intro H s inst src dst cap hf
  unfold invokeConfig
  wasm_run [hf, Lifted.func7]
  exact Must.done (o := .returned s [.i32 4294967295]) ⟨rfl, rfl⟩ rfl

theorem emptyBlockDecoded_holds : emptyBlockDecoded := by
  intro H s inst src dst mem hf him hm hb hz
  have hread : mem.read src.toNat 1 = 0 := by simp [MemInst.read, hz]
  have hfit : ¬ mem.size < src.toNat + 1 := by omega
  have h10 : (1 : BitVec 32) ≠ 0 := by decide
  have hsmod : src.toNat % 4294967296 = src.toNat := Nat.mod_eq_of_lt src.isLt
  unfold invokeConfig
  wasm_run [hf, Lifted.func7, him, hm, hread, hfit, h10, hsmod, Num.iadd_eq, BitVec.add_zero,
    Num.iadd, Num.isub, Num.iand, Num.ishrU, Num.iltU, Num.igtU, Num.igeU,
    Num.ileU, Num.ieq, Num.ieqz, Num.bool, BitVec.toNat_ofNat, BitVec.toNat_zero,
    BitVec.toNat_one, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNatLT, BitVec.toNat_eq, BitVec.zero_and,
    Nat.add_zero, Nat.zero_add, Nat.le_refl, Nat.lt_irrefl]
  exact Must.done (o := .returned s [.i32 0]) ⟨rfl, rfl⟩ rfl

theorem artifactInitializes_holds : artifactInitializes := by
  intro H
  exact ⟨initial.1, initial.2, initial_instance H⟩

end Proofs
