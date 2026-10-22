import FVA.Proof.Numerics.ConvertLemmas

/-!
# Conversions and comparisons

The executable conversions and comparisons equal the spec's (or return an allowed element).
-/

namespace FVA.Wasm.Num

open FVal Impl ConvertLemmas Classical

theorem truncInt_eq {F : FloatFormat} {z : FVal} (hz : z.IsNum) :
    truncInt F z = truncR (z.toReal F) := by
  rw [toReal_eq_sig z hz]
  have hp : 0 ≤ (sig F z : ℝ) * 2 ^ ex F z :=
    mul_nonneg (Nat.cast_nonneg _) (le_of_lt (zpow_pos (by norm_num) _))
  rw [truncR_signed z.neg hp, floor_dyadic]
  simp only [truncInt, Bool.cond_eq_ite]
  rfl

theorem ftruncU_eq (F : FloatFormat) (N : ℕ) (z : FVal) : Impl.ftruncU F N z = ftruncU F N z := by
  cases z <;> simp [Impl.ftruncU, ftruncU, isNaN, isInf, IsNaN, IsInf, ← Bool.decide_and]
  all_goals rw [truncInt_eq (by trivial)]

theorem ftruncS_eq (F : FloatFormat) (N : ℕ) (z : FVal) : Impl.ftruncS F N z = ftruncS F N z := by
  cases z <;> simp [Impl.ftruncS, ftruncS, isNaN, isInf, IsNaN, IsInf, ← Bool.decide_and]
  all_goals rw [truncInt_eq (by trivial)]

theorem ftruncSatU_eq (F : FloatFormat) (N : ℕ) (z : FVal) :
    Impl.ftruncSatU F N z = ftruncSatU F N z := by
  cases z with
  | inf s => cases s <;> simp [Impl.ftruncSatU, ftruncSatU, isNaN, isInf, IsNaN, FVal.neg]
  | _ =>
    simp [Impl.ftruncSatU, ftruncSatU, isNaN, isInf, IsNaN]
    all_goals rw [truncInt_eq (by trivial)]

theorem ftruncSatS_eq (F : FloatFormat) (N : ℕ) (z : FVal) :
    Impl.ftruncSatS F N z = ftruncSatS F N z := by
  cases z with
  | inf s => cases s <;> simp [Impl.ftruncSatS, ftruncSatS, isNaN, isInf, IsNaN, FVal.neg]
  | _ =>
    simp [Impl.ftruncSatS, ftruncSatS, isNaN, isInf, IsNaN]
    all_goals rw [truncInt_eq (by trivial)]

theorem fconvertU_mem {F : FloatFormat} (hF : F.Sane) {M : ℕ} (i : BitVec M) :
    Impl.fconvertU F i ∈ fconvertU F i := ofInt_mem hF i.toNat

theorem fconvertS_mem {F : FloatFormat} (hF : F.Sane) {M : ℕ} (i : BitVec M) :
    Impl.fconvertS F i ∈ fconvertS F i := ofInt_mem hF (signed i)

theorem fpromote_mem {z : FVal} (hz : z.WF f32fmt) : Impl.fpromote z ∈ fpromote z := by
  cases z with
  | nan s n =>
    by_cases hc : n = f32fmt.canon
    · subst n
      have hshift : Nat.lor (f32fmt.canon * 2 ^ (f64fmt.M - f32fmt.M)) f64fmt.canon =
          f64fmt.canon := by decide
      change nan s (Nat.lor (f32fmt.canon * 2 ^ (f64fmt.M - f32fmt.M)) f64fmt.canon) ∈ _
      rw [hshift]
      simpa [fpromote] using nan_mem_nil f64fmt s
    · have hs : n * 2 ^ (f64fmt.M - f32fmt.M) < 2 ^ f64fmt.M := by
        norm_num [WF, f32fmt] at hz
        norm_num [f64fmt, f32fmt]
        omega
      have hm := nan_mem_noncanon (F := f64fmt) (s := s) (by decide)
        (Nat.right_le_or (n := n * 2 ^ (f64fmt.M - f32fmt.M)) (m := f64fmt.canon))
        (Nat.or_lt_two_pow hs (show f64fmt.canon < 2 ^ f64fmt.M by decide))
      simpa [Impl.fpromote, fpromote, hc, IsNaN] using hm
  | inf s => simp [Impl.fpromote, fpromote, IsNaN, IsInf]
  | normal s m e =>
    simpa [Impl.fpromote, fpromote, isZero, IsNaN, IsInf] using
      promote_num hz (by trivial) (by simp [IsZero])
  | subnormal s m =>
    by_cases hm : m = 0
    · subst m
      simp [Impl.fpromote, fpromote, isZero, IsNaN, IsInf, WF, f64fmt, toReal, IsNum]
    · have h0 : ¬ (subnormal s m).IsZero := by cases m <;> simp_all [IsZero]
      simpa [Impl.fpromote, fpromote, isZero, hm, IsNaN, IsInf] using
        promote_num hz (by trivial) h0

theorem fdemote_mem {z : FVal} (hz : z.WF f64fmt) : Impl.fdemote z ∈ fdemote z := by
  cases z with
  | nan s n =>
    by_cases hc : n = f64fmt.canon
    · subst n
      have hshift : Nat.lor (f64fmt.canon / 2 ^ (f64fmt.M - f32fmt.M)) f32fmt.canon =
          f32fmt.canon := by decide
      change nan s (Nat.lor (f64fmt.canon / 2 ^ (f64fmt.M - f32fmt.M)) f32fmt.canon) ∈ _
      rw [hshift]
      simpa [fdemote] using nan_mem_nil f32fmt s
    · have hs : n / 2 ^ (f64fmt.M - f32fmt.M) < 2 ^ f32fmt.M := by
        norm_num [WF, f64fmt] at hz
        norm_num [f64fmt, f32fmt]
        omega
      have hm := nan_mem_noncanon (F := f32fmt) (s := s) (by decide)
        (Nat.right_le_or (n := n / 2 ^ (f64fmt.M - f32fmt.M)) (m := f32fmt.canon))
        (Nat.or_lt_two_pow hs (show f32fmt.canon < 2 ^ f32fmt.M by decide))
      simpa [Impl.fdemote, fdemote, hc, IsNaN] using hm
  | inf s => simp [Impl.fdemote, fdemote, IsNaN, IsInf]
  | normal s m e =>
    simpa [Impl.fdemote, fdemote, isZero, IsNaN, IsInf, IsZero] using
      demote_num (z := normal s m e) (by trivial) (by simp [IsZero])
  | subnormal s m =>
    by_cases hm : m = 0
    · subst m
      simp [Impl.fdemote, fdemote, isZero, IsNaN, IsInf, IsZero]
    · have h0 : ¬ (subnormal s m).IsZero := by cases m <;> simp_all [IsZero]
      simpa [Impl.fdemote, fdemote, isZero, hm, IsNaN, IsInf, h0] using
        demote_num (z := subnormal s m) (by trivial) h0

theorem feq_eq (z₁ z₂ : FVal) : Impl.feq z₁ z₂ = feq z₁ z₂ := by
  simp only [Impl.feq, feq, isNaN_decide, isZero_decide, ← Bool.decide_or,
    ← Bool.decide_and, Bool.cond_decide]

theorem fne_eq (z₁ z₂ : FVal) : Impl.fne z₁ z₂ = fne z₁ z₂ := by
  simp only [Impl.fne, fne, isNaN_decide, isZero_decide, ← Bool.decide_or,
    ← Bool.decide_and, Bool.cond_decide]

theorem flt_eq (F : FloatFormat) (z₁ z₂ : FVal) : Impl.flt F z₁ z₂ = flt F z₁ z₂ := by
  cases z₁ <;> cases z₂ <;>
    simp [Impl.flt, flt, isNaN, isInf, IsNaN, FVal.neg, isZero_decide, ← Bool.decide_and]
  all_goals first
    | rw [ltNum_decide (by trivial) (by trivial)]; simp
    | cases_type* Bool <;> simp

theorem fgt_eq (F : FloatFormat) (z₁ z₂ : FVal) : Impl.fgt F z₁ z₂ = fgt F z₁ z₂ := by
  cases z₁ <;> cases z₂ <;>
    simp [Impl.fgt, fgt, isNaN, isInf, IsNaN, FVal.neg, isZero_decide, ← Bool.decide_and]
  all_goals first
    | rw [ltNum_decide (by trivial) (by trivial)]; simp
    | cases_type* Bool <;> simp

theorem fle_eq (F : FloatFormat) (z₁ z₂ : FVal) : Impl.fle F z₁ z₂ = fle F z₁ z₂ := by
  cases z₁ <;> cases z₂ <;>
    simp [Impl.fle, fle, isNaN, isInf, IsNaN, FVal.neg, isZero_decide, ← Bool.decide_and]
  all_goals first
    | rw [leNum_decide (by trivial) (by trivial)]; simp
    | cases_type* Bool <;> simp

theorem fge_eq (F : FloatFormat) (z₁ z₂ : FVal) : Impl.fge F z₁ z₂ = fge F z₁ z₂ := by
  cases z₁ <;> cases z₂ <;>
    simp [Impl.fge, fge, isNaN, isInf, IsNaN, FVal.neg, isZero_decide, ← Bool.decide_and]
  all_goals first
    | rw [leNum_decide (by trivial) (by trivial)]; simp
    | cases_type* Bool <;> simp

end FVA.Wasm.Num
