import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum

namespace IRound

/-- The exact real value of the finite, positive, normal binary64 encoding
    0x3fdfffffffffffff: exponent field 1021, fraction field 2^52 - 1.
    The unbiased exponent is 1021 - 1023 = -2. -/
def input : ℚ := (1 + (4503599627370495 : ℚ) / 2 ^ 52) / 2 ^ 2

/-- Ties are allowed: a nearest integer has no strictly closer competitor. -/
def Nearest (x : ℚ) (n : ℤ) : Prop :=
  ∀ m : ℤ, |x - (n : ℚ)| ≤ |x - (m : ℚ)|

theorem input_exact : input = 9007199254740991 / 18014398509481984 := by
  norm_num [input]

theorem input_in_range : 0 ≤ input ∧ input ≤ 2147483647 := by
  norm_num [input]

theorem zero_strictly_closer : |input - (0 : ℚ)| < |input - (1 : ℚ)| := by
  norm_num [input]

theorem one_not_nearest : ¬ Nearest input 1 := by
  intro h
  exact (not_le_of_gt zero_strictly_closer) (h 0)

/-- When execution returns 1 at this input, it violates R1. The execution
    premise is checked on the shipped bytes by verify_artifact.py, not assumed
    as a Lean axiom or represented by a replacement implementation. -/
theorem r1_counterexample :
    0 ≤ input ∧ input ≤ 2147483647 ∧ ¬ Nearest input 1 := by
  exact ⟨input_in_range.1, input_in_range.2, one_not_nearest⟩

end IRound

#print axioms IRound.r1_counterexample
