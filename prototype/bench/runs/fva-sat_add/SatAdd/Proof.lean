import SatAdd.Spec
import FVA

namespace SatAdd.Proof
open FVA.Wasm

-- 33 signed bits suffice to hold the exact sum of two signed 32-bit integers.
def wideSum (a b : BitVec 32) : BitVec 33 :=
  a.signExtend 33 + b.signExtend 33

def wideResult (a b : BitVec 32) : BitVec 32 :=
  let s := wideSum a b
  if (2147483647#33).slt s then 2147483647#32
  else if s.slt 6442450944#33 then 2147483648#32
  else s.setWidth 32

def machineResult (a b : BitVec 32) : BitVec 32 :=
  if ((if b.slt 0#32 then 1#32 else 0#32) ^^^
      (if (a + b).slt a then 1#32 else 0#32)) ≠ 0#32 then
    (a + b).sshiftRight 31 ^^^ 2147483648#32
  else a + b

theorem signed_bounds (x : BitVec 32) :
    -2147483648 ≤ x.toInt ∧ x.toInt ≤ 2147483647 := by
  have hlo := BitVec.le_toInt x
  have hhi := BitVec.toInt_lt (x := x)
  change -2147483648 ≤ x.toInt at hlo
  change x.toInt < 2147483648 at hhi
  omega

theorem sum_toInt (a b : BitVec 32) :
    (a + b).toInt =
      if 2147483647 < a.toInt + b.toInt then a.toInt + b.toInt - 4294967296
      else if a.toInt + b.toInt < -2147483648 then a.toInt + b.toInt + 4294967296
      else a.toInt + b.toInt := by
  have ha := signed_bounds a
  have hb := signed_bounds b
  rw [BitVec.toInt_add]
  change (a.toInt + b.toInt).bmod 4294967296 = _
  by_cases hhi : 2147483647 < a.toInt + b.toInt
  · rw [ite_eq_left hhi]
    unfold Int.bmod
    dsimp only
    split <;> omega
  · rw [ite_eq_right hhi]
    by_cases hlo : a.toInt + b.toInt < -2147483648
    · rw [ite_eq_left hlo]
      unfold Int.bmod
      dsimp only
      split <;> omega
    · rw [ite_eq_right hlo]
      unfold Int.bmod
      dsimp only
      split <;> omega

theorem sign_mask (x : BitVec 32) :
    x.sshiftRight 31 ^^^ 2147483648#32 =
      if x.toInt < 0 then 2147483647#32 else 2147483648#32 := by
  have hx := signed_bounds x
  have hs : x.sshiftRight 31 =
      if x.toInt < 0 then 4294967295#32 else 0#32 := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
    by_cases h : x.toInt < 0
    · rw [ite_eq_left h]
      change x.toInt / 2147483648 = -1
      omega
    · rw [ite_eq_right h]
      change x.toInt / 2147483648 = 0
      omega
  rw [hs]
  by_cases h : x.toInt < 0 <;> simp only [h, ite_true, ite_false] <;> decide

theorem wideSum_toInt (a b : BitVec 32) :
    (wideSum a b).toInt = a.toInt + b.toInt := by
  have haLo := BitVec.le_toInt a
  have haHi := BitVec.toInt_lt (x := a)
  have hbLo := BitVec.le_toInt b
  have hbHi := BitVec.toInt_lt (x := b)
  change -2147483648 ≤ a.toInt at haLo
  change a.toInt < 2147483648 at haHi
  change -2147483648 ≤ b.toInt at hbLo
  change b.toInt < 2147483648 at hbHi
  rw [wideSum, BitVec.toInt_add,
    BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 33),
    BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 33)]
  apply Int.bmod_eq_of_le
  · change -4294967296 ≤ a.toInt + b.toInt
    omega
  · change a.toInt + b.toInt < 4294967296
    omega

theorem wideSum_narrow (a b : BitVec 32) :
    (wideSum a b).setWidth 32 = a + b := by
  rw [wideSum, BitVec.setWidth_add _ _ (by decide : 32 ≤ 33)]
  have narrow (x : BitVec 32) : (x.signExtend 33).setWidth 32 = x := by
    ext i hi
    simp [BitVec.getElem_setWidth, BitVec.getElem_signExtend, hi,
      show i < 33 by omega]
  rw [narrow, narrow]

theorem sum_encoding (a b : BitVec 32) :
    a + b = BitVec.ofInt 32 (a.toInt + b.toInt) := by
  rw [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt]

-- Kernel-only integer arithmetic justifies the compiler's overflow test and mask.
theorem machineResult_eq (a b : BitVec 32) :
    machineResult a b = wideResult a b := by
  have ha := signed_bounds a
  have hb := signed_bounds b
  have hs := sum_toInt a b
  unfold machineResult wideResult
  rw [sign_mask]
  simp only [BitVec.slt_iff_toInt_lt, wideSum_toInt,
    show (0#32).toInt = 0 from rfl,
    show (2147483647#33).toInt = 2147483647 from rfl,
    show (6442450944#33).toInt = -2147483648 from rfl]
  by_cases hhi : 2147483647 < a.toInt + b.toInt
  · have hbn : ¬ b.toInt < 0 := by omega
    have hsa : (a + b).toInt < a.toInt := by simp only [hhi, ite_true] at hs; omega
    have hsn : (a + b).toInt < 0 := by simp only [hhi, ite_true] at hs; omega
    simp [hhi, hbn, hsa, hsn, -BitVec.toInt_add]
  · by_cases hlo : a.toInt + b.toInt < -2147483648
    · have hbn : b.toInt < 0 := by omega
      have hsa : ¬ (a + b).toInt < a.toInt := by
        simp only [hhi, hlo, ite_true, ite_false] at hs
        omega
      have hsn : ¬ (a + b).toInt < 0 := by
        simp only [hhi, hlo, ite_true, ite_false] at hs
        omega
      simp [hhi, hlo, hbn, hsa, hsn, -BitVec.toInt_add]
    · have hsa : ((a + b).toInt < a.toInt) ↔ b.toInt < 0 := by
        simp only [hhi, hlo, ite_false] at hs
        omega
      by_cases hbn : b.toInt < 0 <;>
        simp [hhi, hlo, hsa, hbn, wideSum_narrow, -BitVec.toInt_add]

theorem invoke_result (a b : BitVec 32) :
    invoke Lifted.sat_add 30 [.i32 a, .i32 b] = some [.i32 (wideResult a b)] := by
  rw [← machineResult_eq]
  wasm_sim [Lifted.sat_add]
  unfold machineResult
  simp only [show (31#32).toNat % 32 = 31 from rfl]
  simp only [BitVec.ofNat_eq_ofNat]
  by_cases hb : b.slt 0#32 = true <;>
    by_cases ha : (a + b).slt a = true <;> simp [hb, ha]

theorem r1_holds : r1 := by
  intro a b hlo hhi
  have hi : ¬ (2147483647#33).slt (wideSum a b) := by
    rw [BitVec.slt_iff_toInt_lt, wideSum_toInt]
    change ¬ (2147483647 < a.toInt + b.toInt)
    omega
  have lo : ¬ (wideSum a b).slt 6442450944#33 := by
    rw [BitVec.slt_iff_toInt_lt, wideSum_toInt]
    change ¬ (a.toInt + b.toInt < -2147483648)
    omega
  apply returns_of_invoke rfl
  refine ⟨30, ?_⟩
  simpa only [wideResult, hi, lo, Bool.false_eq_true, ite_false, wideSum_narrow, sum_encoding]
    using invoke_result a b

theorem r2_holds : r2 := by
  intro a b h
  have hi : (2147483647#33).slt (wideSum a b) := by
    rw [BitVec.slt_iff_toInt_lt, wideSum_toInt]
    exact h
  apply returns_of_invoke rfl
  refine ⟨30, ?_⟩
  simpa only [wideResult, hi, ite_true] using invoke_result a b

theorem r3_holds : r3 := by
  intro a b h
  have hi : ¬ (2147483647#33).slt (wideSum a b) := by
    rw [BitVec.slt_iff_toInt_lt, wideSum_toInt]
    change ¬ (2147483647 < a.toInt + b.toInt)
    omega
  have lo : (wideSum a b).slt 6442450944#33 := by
    rw [BitVec.slt_iff_toInt_lt, wideSum_toInt]
    exact h
  apply returns_of_invoke rfl
  refine ⟨30, ?_⟩
  simpa only [wideResult, hi, lo, Bool.false_eq_true, ite_true, ite_false] using invoke_result a b

end SatAdd.Proof
