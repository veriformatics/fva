import Proofs.Model
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Proofs

/-- Rational Taylor polynomial and an analytic remainder bound. -/
def logSeries (q : ℚ) : ℚ :=
  let x := (q - 1) / (q + 1)
  2 * (Finset.range 16).sum (fun i => x ^ (2 * i + 1) / (2 * i + 1))

def logError (q : ℚ) : ℚ :=
  let x := (q - 1) / (q + 1)
  2 * |x| ^ 33 / (1 - x ^ 2)

theorem logSeries_bound (q : ℚ) (hq : 0 < q) :
    |Real.log (q : ℝ) - (logSeries q : ℝ)| ≤ (logError q : ℝ) := by
  let x : ℝ := ((q : ℝ) - 1) / ((q : ℝ) + 1)
  have hp : 0 < (q : ℝ) := by exact_mod_cast hq
  have hx : |x| < 1 := by
    rw [abs_lt]
    dsimp [x]
    constructor
    · apply (lt_div_iff₀ (by linarith)).2; linarith
    · apply (div_lt_iff₀ (by linarith)).2; linarith
  have he : (1 + x) / (1 - x) = (q : ℝ) := by dsimp [x]; field_simp; ring
  have h := Real.sum_range_sub_log_div_le hx 16
  rw [he] at h
  have hs : (logSeries q : ℝ) =
      2 * (Finset.range 16).sum (fun i => x ^ (2 * i + 1) / (2 * i + 1)) := by
    simp [logSeries, x, Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_sub,
      Rat.cast_add, Rat.cast_pow, Rat.cast_natCast]
  have herr : (logError q : ℝ) = 2 * |x| ^ 33 / (1 - x ^ 2) := by
    simp [logError, x, Rat.cast_div, Rat.cast_mul, Rat.cast_sub,
      Rat.cast_add, Rat.cast_pow, Rat.cast_abs]
  rw [hs, herr]
  have hab : |Real.log (q : ℝ) - 2 * ∑ i ∈ Finset.range 16,
      x ^ (2 * i + 1) / (2 * i + 1)| =
      2 * |1 / 2 * Real.log (q : ℝ) - ∑ i ∈ Finset.range 16,
      x ^ (2 * i + 1) / (2 * i + 1)| := by
    calc
      _ = |2 * (1 / 2 * Real.log (q : ℝ) - ∑ i ∈ Finset.range 16,
          x ^ (2 * i + 1) / (2 * i + 1))| := by congr 1; ring
      _ = _ := by rw [abs_mul]; norm_num
  rw [hab]
  norm_num at h
  convert mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring

/-- Range reduction by a power of two, checked entirely over rationals. -/
theorem log_certificate (q : ℚ) (k : Nat) (lo hi : ℚ)
    (hq : 0 < q)
    (hl : lo ≤ logSeries (q / 2 ^ k) + k * logSeries 2 -
      (logError (q / 2 ^ k) + k * logError 2))
    (hu : logSeries (q / 2 ^ k) + k * logSeries 2 +
      (logError (q / 2 ^ k) + k * logError 2) ≤ hi) :
    (lo : ℝ) ≤ Real.log q ∧ Real.log q ≤ (hi : ℝ) := by
  have hq' : 0 < q / 2 ^ k := div_pos hq (by positivity)
  have h₁ := abs_le.mp (logSeries_bound (q / 2 ^ k) hq')
  have h₂ := abs_le.mp (logSeries_bound 2 (by norm_num))
  norm_num only [Rat.cast_ofNat] at h₂
  have he : Real.log (q : ℝ) = Real.log ((q / 2 ^ k : ℚ) : ℝ) + k * Real.log 2 := by
    push_cast
    rw [Real.log_div (by exact_mod_cast ne_of_gt hq) (by positivity), Real.log_pow]
    ring
  have hl' : (lo : ℝ) ≤ (logSeries (q / 2 ^ k) : ℝ) + k * (logSeries 2 : ℝ) -
      ((logError (q / 2 ^ k) : ℝ) + k * (logError 2 : ℝ)) := by exact_mod_cast hl
  have hu' : (logSeries (q / 2 ^ k) : ℝ) + k * (logSeries 2 : ℝ) +
      ((logError (q / 2 ^ k) : ℝ) + k * (logError 2 : ℝ)) ≤ hi := by exact_mod_cast hu
  rw [he]
  constructor <;> nlinarith [h₁.1, h₁.2, h₂.1, h₂.2, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- Interval evaluation of a linear combination of natural logarithms. -/
def lowerTerm (lb ub : Nat → ℚ) (p : ℚ × Nat) : ℚ :=
  if 0 ≤ p.1 then p.1 * lb p.2 else p.1 * ub p.2

def upperTerm (lb ub : Nat → ℚ) (p : ℚ × Nat) : ℚ :=
  if 0 ≤ p.1 then p.1 * ub p.2 else p.1 * lb p.2

theorem evalLogs_bounds (lb ub : Nat → ℚ)
    (hb : ∀ n, (lb n : ℝ) ≤ Real.log n ∧ Real.log n ≤ (ub n : ℝ))
    (cs : List (ℚ × Nat)) :
    ((cs.map (lowerTerm lb ub)).sum : ℝ) ≤ evalLogs cs ∧
    evalLogs cs ≤ ((cs.map (upperTerm lb ub)).sum : ℝ) := by
  induction cs with
  | nil => simp [evalLogs]
  | cons p ps ih =>
    have h := hb p.2
    have ht : (lowerTerm lb ub p : ℝ) ≤ (p.1 : ℝ) * Real.log p.2 ∧
        (p.1 : ℝ) * Real.log p.2 ≤ (upperTerm lb ub p : ℝ) := by
      by_cases hc : 0 ≤ p.1
      · have hc' : (0 : ℝ) ≤ p.1 := by exact_mod_cast hc
        simpa [lowerTerm, upperTerm, hc] using
          And.intro (mul_le_mul_of_nonneg_left h.1 hc') (mul_le_mul_of_nonneg_left h.2 hc')
      · have hc' : (p.1 : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hc))
        simpa [lowerTerm, upperTerm, hc] using
          And.intro (mul_le_mul_of_nonpos_left h.2 hc') (mul_le_mul_of_nonpos_left h.1 hc')
    simp only [List.map_cons, List.sum_cons, Rat.cast_add]
    change (lowerTerm lb ub p : ℝ) + _ ≤ (p.1 : ℝ) * Real.log p.2 + evalLogs ps ∧
      (p.1 : ℝ) * Real.log p.2 + evalLogs ps ≤ (upperTerm lb ub p : ℝ) + _
    constructor <;> linarith [ih.1, ih.2, ht.1, ht.2]

/-- Monotonicity of log and exp transfers log intervals into factor intervals. -/
theorem exp_bounds (x : ℝ) (a b : ℚ) (ha : 0 < a) (hb : 0 < b)
    (hlo : Real.log (a : ℝ) ≤ x) (hhi : x ≤ Real.log (b : ℝ)) :
    (a : ℝ) ≤ Real.exp x ∧ Real.exp x ≤ (b : ℝ) := by
  constructor
  · simpa [Real.exp_log (by exact_mod_cast ha : (0 : ℝ) < a)] using Real.exp_le_exp.mpr hlo
  · simpa [Real.exp_log (by exact_mod_cast hb : (0 : ℝ) < b)] using Real.exp_le_exp.mpr hhi

end Proofs
