import FVA.Proof.Lib.BlockFacts

namespace FVA.Wasm.Exec.Ref

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Num

@[block_simp] theorem eq32 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    ieq (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = bool (decide (a = b)) := by
  simp only [ieq, ofNat32_toNat ha, ofNat32_toNat hb]
  congr 1

@[block_simp] theorem leU32 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    ileU (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = bool (decide (a ≤ b)) := by
  simp only [ileU, ofNat32_toNat ha, ofNat32_toNat hb]

@[block_simp] theorem shr32_four {a : Nat} (ha : a < 2 ^ 32) :
    ishrU (BitVec.ofNat 32 a) (BitVec.ofNat 32 4) = BitVec.ofNat 32 (a / 16) := by
  simp only [ishrU, ofNat32_toNat ha, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]

@[block_simp] theorem and32_fifteen (a : Nat) :
    iand (BitVec.ofNat 32 a) (BitVec.ofNat 32 15) = BitVec.ofNat 32 (a % 16) := by
  change BitVec.ofNat 32 a &&& BitVec.ofNat 32 (2 ^ 4 - 1) = _
  rw [← BitVec.ofNat_and, Nat.and_two_pow_sub_one_eq_mod]

attribute [block_simp] isub_eq List.getElem?_set_self List.getElem?_set_ne

end FVA.Wasm.Exec.Ref
