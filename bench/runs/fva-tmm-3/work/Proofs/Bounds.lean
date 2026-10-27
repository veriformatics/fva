import Proofs.Model
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

set_option autoImplicit false

namespace Proofs

-- This file contains only kernel-checked supporting proofs, not specifications.
def series (q : ℚ) (n : Nat := 10) : ℚ :=
  2 * ∑ i ∈ Finset.range n, ((q-1)/(q+1))^(2*i+1) / (2*(i : ℚ)+1)

def remainder (q : ℚ) (n : Nat := 10) : ℚ :=
  2 * ((q-1)/(q+1))^(2*n+1) / (1 - ((q-1)/(q+1))^2)

theorem series_bounds (q : ℚ) (hq : 1 ≤ q) (n : Nat) :
    (series q n : ℝ) ≤ Real.log (q : ℝ) ∧
    Real.log (q : ℝ) ≤ ((series q n + remainder q n : ℚ) : ℝ) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  let x : ℝ := ((q : ℝ)-1)/((q : ℝ)+1)
  have hp : 0 < (q : ℝ)+1 := by linarith
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hp.le
  have hx1 : x < 1 := (div_lt_one hp).mpr (by linarith)
  have he : (1+x)/(1-x) = (q : ℝ) := by dsimp [x]; field_simp; ring
  have hl := Real.sum_range_le_log_div hx0 hx1 n
  have hu := Real.log_div_le_sum_range_add hx0 hx1 n
  rw [he] at hl hu
  have hs : (series q n : ℝ) =
      2 * ∑ i ∈ Finset.range n, x^(2*i+1) / (2*i+1 : ℝ) := by
    simp [series, x, Rat.cast_sum]
  have hr : (remainder q n : ℝ) = 2 * x^(2*n+1)/(1-x^2) := by
    simp [remainder, x]
  simp only [mul_div_assoc] at hr
  push_cast
  rw [hs, hr]
  constructor <;> nlinarith [hu]

 theorem log_two : (69314718/100000000 : ℚ) ≤ Real.log 2 ∧
    Real.log 2 ≤ (69314719/100000000 : ℚ) := by
  have h := series_bounds 2 (by norm_num) 10
  have hl : (69314718/100000000 : ℚ) ≤ series 2 10 := by decide +kernel
  have hu : series 2 10 + remainder 2 10 ≤ (69314719/100000000 : ℚ) := by decide +kernel
  constructor
  · exact le_trans (by exact_mod_cast hl) h.1
  · exact le_trans h.2 (by exact_mod_cast hu)

theorem log_certificate (n k : Nat) (q lo hi : ℚ) (hq : 1 ≤ q)
    (he : (n : ℚ) = q * 2^k)
    (hl : lo ≤ series q 10 + k * (69314718/100000000 : ℚ))
    (hu : series q 10 + remainder q 10 + k * (69314719/100000000 : ℚ) ≤ hi) :
    (lo : ℝ) ≤ Real.log n ∧ Real.log n ≤ (hi : ℝ) := by
  have hs := series_bounds q hq 10
  have h2 := log_two
  have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℚ)<1) hq)
  have heR : (n : ℝ) = (q : ℝ) * (2:ℝ)^k := by exact_mod_cast he
  have hlog : Real.log n = Real.log (q : ℝ) + k * Real.log 2 := by
    rw [heR, Real.log_mul (ne_of_gt hqR) (by positivity), Real.log_pow]
  have hlR : (lo : ℝ) ≤ (series q 10 : ℝ) + k * ((69314718/100000000 : ℚ) : ℝ) := by exact_mod_cast hl
  have huR : (series q 10 : ℝ) + (remainder q 10 : ℝ) + k * ((69314719/100000000 : ℚ) : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hu
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2l := mul_le_mul_of_nonneg_left h2.1 hk
  have h2u := mul_le_mul_of_nonneg_left h2.2 hk
  push_cast at hs
  rw [hlog]
  constructor <;> linarith

end Proofs
