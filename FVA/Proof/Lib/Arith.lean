import FVA.Spec.Exec.Numeric

/-!
# Integer operators ↔ `BitVec`/`Nat`/`Int` (U8 L5)

The reviewed integer spec states each operator through `signed`, `ofSigned` and `Nat`
arithmetic modulo `2^N`; claims speak `BitVec` (`slt`, `ult`, `+`). These lemmas connect them.
-/

namespace FVA.Wasm.Num

theorem signed_eq_toInt {N : Nat} (i : BitVec N) : signed i = i.toInt := by
  unfold signed
  rw [BitVec.toInt_eq_toNat_cond]
  rcases N with _ | N
  · simp [BitVec.toNat_of_zero_length]
  · have : i.toNat < 2 ^ N ↔ 2 * i.toNat < 2 ^ (N + 1) := by rw [Nat.pow_succ]; omega
    simp only [Nat.add_sub_cancel, this]
    push_cast; rfl

theorem bool_eq_zero (c : Bool) : bool c = 0#32 ↔ c = false := by
  cases c <;> simp [bool]

theorem iltS_eq_zero {N : Nat} (a b : BitVec N) : iltS a b = 0#32 ↔ ¬ a.slt b := by
  rw [iltS, bool_eq_zero, signed_eq_toInt, signed_eq_toInt, BitVec.slt_iff_toInt_lt]
  simp

theorem iltU_eq_zero {N : Nat} (a b : BitVec N) : iltU a b = 0#32 ↔ ¬ a.ult b := by
  rw [iltU, bool_eq_zero, BitVec.ult_iff_lt, BitVec.lt_def]
  simp

theorem ieqz_eq_zero {N : Nat} (a : BitVec N) : ieqz a = 0 ↔ a ≠ 0 := by
  rw [ieqz, show (0 : BitVec 32) = 0#32 from rfl, bool_eq_zero]
  simp [BitVec.toNat_eq]

theorem iadd_eq {N : Nat} (a b : BitVec N) : iadd a b = a + b :=
  BitVec.eq_of_toNat_eq (by simp [iadd, BitVec.toNat_add])

theorem isub_eq {N : Nat} (a b : BitVec N) : isub a b = a - b := by
  have : a.toNat + 2 ^ N - b.toNat = 2 ^ N - b.toNat + a.toNat := by have := b.isLt; omega
  exact BitVec.eq_of_toNat_eq (by simp [isub, BitVec.toNat_sub, this])

theorem imul_eq {N : Nat} (a b : BitVec N) : imul a b = a * b :=
  BitVec.eq_of_toNat_eq (by simp [imul, BitVec.toNat_mul])

/-- A shift by a constant below the width. -/
theorem ishl_eq {N : Nat} (a b : BitVec N) (h : b.toNat < N) : ishl a b = a <<< b.toNat :=
  BitVec.eq_of_toNat_eq (by simp [ishl, BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt h,
    Nat.shiftLeft_eq])

theorem ixor_eq {N : Nat} (a b : BitVec N) : ixor a b = a ^^^ b := rfl

end FVA.Wasm.Num
