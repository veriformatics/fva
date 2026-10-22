import FVA.Proof.Numerics.SqrtLemmas
import Mathlib.Data.Nat.Sqrt

/-!
# Square root

The digit-by-digit `isqrt` is `Nat.sqrt`. An inexact root, strictly between consecutive fine-grid
integers, rounds like the midpoint.
-/

namespace FVA.Wasm.Num

open FVal Impl

lemma isqrtAux_eq (fuel n : ℕ) (hn : n < 4 ^ fuel) :
    isqrtAux fuel n = Nat.sqrt n := by
  induction fuel generalizing n with
  | zero =>
    have : n = 0 := by simpa using hn
    subst n
    rfl
  | succ fuel ih =>
    have hd : n / 4 < 4 ^ fuel := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).2
      simpa [pow_succ] using hn
    rw [isqrtAux, ih (n / 4) hd]
    have hlo := Nat.sqrt_le (n / 4)
    have hhi := Nat.lt_succ_sqrt (n / 4)
    have hm := Nat.mod_lt n (by decide : 0 < 4)
    have he := Nat.div_add_mod n 4
    cases hc : Nat.blt n ((2 * Nat.sqrt (n / 4) + 1) * (2 * Nat.sqrt (n / 4) + 1))
    · simp only [Bool.cond_false]
      apply Nat.eq_sqrt.2
      have hc' := nblt_false.1 hc
      constructor
      · exact hc'
      · nlinarith
    · simp only [Bool.cond_true]
      apply Nat.eq_sqrt.2
      constructor
      · calc
          2 * Nat.sqrt (n / 4) * (2 * Nat.sqrt (n / 4)) =
              4 * (Nat.sqrt (n / 4) * Nat.sqrt (n / 4)) := by ring
          _ ≤ 4 * (n / 4) := Nat.mul_le_mul_left 4 hlo
          _ ≤ n := by omega
      · exact nblt_true.1 hc

theorem isqrt_eq (n : ℕ) : isqrt n = Nat.sqrt n := by
  apply isqrtAux_eq
  calc n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
    _ ≤ 2 ^ (2 * (Nat.log2 n / 2 + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 4 ^ (Nat.log2 n / 2 + 1) := by rw [pow_mul]; norm_num

lemma sqrt_round_mem {F : FloatFormat} (hF : F.Sane) {n : ℕ}
    (hn : 4 ^ (F.M + 2) ≤ n) (u : ℤ) :
    (bif Nat.beq (isqrt n * isqrt n) n then roundDyadic F false (isqrt n) 1 u
      else roundDyadic F false (2 * isqrt n + 1) 2 u) ∈
      ieee F (Real.sqrt (n : ℝ) * 2 ^ u) := by
  set r := isqrt n with hrdef
  have hrN : r = Nat.sqrt n := isqrt_eq n
  have hrbound : 2 ^ (F.M + 2) ≤ r := by
    rw [hrN, Nat.le_sqrt]
    calc 2 ^ (F.M + 2) * 2 ^ (F.M + 2) = 4 ^ (F.M + 2) := by
            rw [← mul_pow]; norm_num
      _ ≤ n := hn
  have hr0 : 0 < r := lt_of_lt_of_le (Nat.two_pow_pos _) hrbound
  have hrmin : 2 ^ (F.M + 1) ≤ r :=
    le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hrbound
  by_cases he : r * r = n
  · have hs : Real.sqrt (n : ℝ) = r := by
      have heR : (r : ℝ) * r = n := by exact_mod_cast he
      rw [← heR, Real.sqrt_mul_self (Nat.cast_nonneg _)]
    simpa [he, hs] using roundDyadic_mem hF false hr0 Nat.one_pos u
  · have hb : Nat.beq (r * r) n = false := by
      rw [← Bool.not_eq_true, Nat.beq_eq]
      exact he
    rw [hb]
    simp only [Bool.cond_false]
    have hlN : r * r < n := by have := Nat.sqrt_le n; rw [← hrN] at this; omega
    have huN : n < (r + 1) * (r + 1) := by
      rw [hrN]; exact Nat.lt_succ_sqrt n
    have hl : (r : ℝ) < Real.sqrt (n : ℝ) := by
      apply (Real.lt_sqrt (Nat.cast_nonneg _)).2
      exact_mod_cast (by simpa [pow_two] using hlN : r ^ 2 < n)
    have hu : Real.sqrt (n : ℝ) < (r : ℝ) + 1 := by
      apply (Real.sqrt_lt' (by positivity)).2
      exact_mod_cast (by simpa [pow_two] using huN : n < (r + 1) ^ 2)
    apply (ieee_iff_grid hF _ _).2
    rw [roundDyadic_eq F false (by omega : 0 < 2 * r + 1) (by decide : 0 < 2)]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, Nat.cast_ofNat]
    apply gridRound_fine_interval hrmin
    · apply mul_lt_mul_of_pos_right _ (two_zpow_pos u)
      push_cast
      linarith
    · apply mul_lt_mul_of_pos_right _ (two_zpow_pos u)
      push_cast
      linarith
    · exact mul_lt_mul_of_pos_right hl (two_zpow_pos u)
    · exact mul_lt_mul_of_pos_right hu (two_zpow_pos u)

lemma sqrtNum_mem {F : FloatFormat} (hF : F.Sane) {z : FVal}
    (hz : z.IsNum) (h0 : ¬ z.IsZero) (hs : z.neg = false) :
    sqrtNum F z ∈ ieee F (Real.sqrt (z.toReal F)) := by
  let e := ex F z
  let p := e % 2
  let h := (e - p) / 2
  let k := F.M + 2
  let n := sig F z * 2 ^ p.toNat * 4 ^ k
  have hsig := sig_pos (F := F) hz h0
  have hp : 0 ≤ p := Int.emod_nonneg _ (by decide)
  have he : e = p + 2 * h := by dsimp [p, h]; omega
  have hn : 4 ^ k ≤ n := by
    dsimp [n]
    have ha : 1 ≤ sig F z * 2 ^ p.toNat := Nat.mul_pos hsig (Nat.two_pow_pos _)
    simpa using Nat.mul_le_mul_right (4 ^ k) ha
  have h4 : (4 : ℝ) ^ k = 2 ^ (2 * (k : ℤ)) := by
    rw [show 2 * (k : ℤ) = ((2 * k : ℕ) : ℤ) by push_cast; rfl,
      zpow_natCast, pow_mul]
    norm_num
  have hv : z.toReal F = (n : ℝ) * ((2 : ℝ) ^ (h - k)) ^ 2 := by
    rw [toReal_eq_sig z hz, hs]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    change (sig F z : ℝ) * 2 ^ e = (n : ℝ) * (2 ^ (h - k)) ^ 2
    dsimp only [n]
    push_cast
    rw [h4, ← zpow_natCast (2 : ℝ) p.toNat, Int.toNat_of_nonneg hp,
      ← zpow_natCast ((2 : ℝ) ^ (h - k)) 2, ← zpow_mul,
      mul_assoc, ← zpow_add₀ two_ne_zero, mul_assoc, ← zpow_add₀ two_ne_zero]
    congr 1
    congr 1
    omega
  have hsqrt : Real.sqrt (z.toReal F) = Real.sqrt (n : ℝ) * 2 ^ (h - k) := by
    rw [hv, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (two_zpow_pos _).le]
  rw [hsqrt]
  exact sqrt_round_mem hF hn (h - k)

/-- `Impl.fsqrt` returns an allowed result. -/
theorem fsqrt_mem {F : FloatFormat} (hF : F.Sane) {z : FVal} (hz : z.WF F) :
    Impl.fsqrt F z ∈ fsqrt F z := by
  have hnil : nanOf F [] ∈ nans F [] := nanOf_mem hF.hM (by simp)
  cases z with
  | nan s n =>
    simpa [Impl.fsqrt, fsqrt, isNaN, IsNaN] using
      nanOf_mem hF.hM (zs := [nan s n]) (by simpa using hz)
  | inf s =>
    cases s with
    | false => simp [Impl.fsqrt, fsqrt, isNaN, isInf, IsNaN, FVal.neg]
    | true => simpa [Impl.fsqrt, fsqrt, isNaN, isInf, IsNaN, FVal.neg] using hnil
  | normal s m e =>
    cases s with
    | false =>
      simpa [Impl.fsqrt, fsqrt, isNaN, isInf, isZero, IsNaN, IsZero, FVal.neg] using
        sqrtNum_mem hF (z := normal false m e) trivial (by simp [IsZero]) rfl
    | true =>
      simpa [Impl.fsqrt, fsqrt, isNaN, isInf, isZero, IsNaN, IsZero, FVal.neg] using hnil
  | subnormal s m =>
    cases m with
    | zero =>
      cases s <;> simp [Impl.fsqrt, fsqrt, isNaN, isInf, isZero, IsNaN, IsZero, FVal.neg]
    | succ m =>
      cases s with
      | false =>
        simpa [Impl.fsqrt, fsqrt, isNaN, isInf, isZero, IsNaN, IsZero, FVal.neg] using
          sqrtNum_mem hF (z := subnormal false (m + 1)) trivial (by simp [IsZero]) rfl
      | true =>
        simpa [Impl.fsqrt, fsqrt, isNaN, isInf, isZero, IsNaN, IsZero, FVal.neg] using hnil

end FVA.Wasm.Num
