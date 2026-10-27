import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace TMM

/-- Elementary rational lower enclosure, with no floating-point computation. -/
def logLower (q : ℚ) : ℚ :=
  if 1 ≤ q then 2 * (q-1)/(q+1) else 1 - 1/q

theorem log_lower (q : ℚ) (hq : 0 < q) :
    (logLower q : ℝ) ≤ Real.log (q : ℝ) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  unfold logLower
  split_ifs with h
  · have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast h
    have hh := Real.le_log_one_add_of_nonneg (sub_nonneg.mpr hq1)
    push_cast
    convert hh using 1 <;> congr 1 <;> ring
  · have hh := Real.one_sub_inv_le_log_of_pos hqr
    push_cast
    simpa [one_div] using hh

end TMM
