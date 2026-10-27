import Proofs.Spec

namespace Verification

def z (q : ℚ) : ℚ := (q - 1) / (q + 1)
def logMid (q : ℚ) : ℚ :=
  2 * ∑ j ∈ Finset.range 3, z q ^ (2 * j + 1) / (2 * j + 1)
def logErr (q : ℚ) : ℚ := 2 * |z q| ^ 7 / (1 - z q ^ 2)
def logLo (q : ℚ) : ℚ := logMid q - logErr q
def logHi (q : ℚ) : ℚ := logMid q + logErr q

theorem certifiedLog (q : ℚ) (hq : 0 < q) :
    (logLo q : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ (logHi q : ℝ) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hp : (q : ℝ) + 1 ≠ 0 := by linarith
  have hz : |(z q : ℝ)| < 1 := by
    simp only [z, Rat.cast_div, Rat.cast_sub, Rat.cast_one, Rat.cast_add]
    apply abs_lt.mpr
    constructor
    · apply (lt_div_iff₀ (by linarith : 0 < (q : ℝ) + 1)).mpr
      linarith
    · apply (div_lt_iff₀ (by linarith : 0 < (q : ℝ) + 1)).mpr
      linarith
  have heq : (1 + (z q : ℝ)) / (1 - (z q : ℝ)) = (q : ℝ) := by
    simp only [z, Rat.cast_div, Rat.cast_sub, Rat.cast_one, Rat.cast_add]
    field_simp
    ; ring
  have h := Real.sum_range_sub_log_div_le hz 3
  rw [heq] at h
  have hm : (logMid q : ℝ) = 2 * ∑ j ∈ Finset.range 3,
      (z q : ℝ) ^ (2 * j + 1) / (2 * j + 1) := by
    simp [logMid]
  have he : (logErr q : ℝ) = 2 * (|(z q : ℝ)| ^ 7 / (1 - (z q : ℝ) ^ 2)) := by
    simp [logErr, mul_div_assoc]
  have hh := abs_le.mp h
  norm_num only at hh
  constructor
  · simp only [logLo, Rat.cast_sub]
    rw [hm, he]
    linear_combination 2 * hh.1
  · simp only [logHi, Rat.cast_add]
    rw [hm, he]
    linear_combination 2 * hh.2

end Verification
