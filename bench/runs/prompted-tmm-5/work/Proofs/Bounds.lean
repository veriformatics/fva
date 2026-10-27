import Proofs.Spec
namespace Verification
-- A rational lower bound for log(q), from two terms of the atanh series.
def logLower (q : ℚ) : ℚ :=
  let z := (q-1)/(q+1)
  2 * (z + z^3/3) - 2 * |z|^5/(1-z^2)

theorem logLower_sound (q : ℚ) (hq : 0 < q) :
    (logLower q : ℝ) ≤ Real.log (q : ℝ) := by
  let z : ℝ := ((q : ℝ)-1)/((q : ℝ)+1)
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hz : |z| < 1 := by
    rw [abs_lt]
    dsimp [z]
    constructor
    · apply (lt_div_iff₀ (by linarith : (0 : ℝ) < q+1)).2
      linarith
    · apply (div_lt_iff₀ (by linarith : (0 : ℝ) < q+1)).2
      linarith
  have he : (1+z)/(1-z) = (q : ℝ) := by dsimp [z]; field_simp; ring
  have h := Real.sum_range_sub_log_div_le hz 2
  rw [he] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  have hh := (abs_le.mp h).1
  dsimp [logLower]
  push_cast
  change 2 * (z + z^3/3) - 2 * |z|^5/(1-z^2) ≤ Real.log (q : ℝ)
  simp only [mul_div_assoc]
  linarith
end Verification
