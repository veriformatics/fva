import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

namespace IRound

/-- The exact real value of the finite binary64 input 0x3fdfffffffffffff. -/
noncomputable def x : ℝ := 9007199254740991 / 18014398509481984

/-- R1's nearest-integer predicate; ties are allowed. -/
def IsNearest (v : ℝ) (n : ℤ) : Prop :=
  ∀ m : ℤ, |v - (n : ℝ)| ≤ |v - (m : ℝ)|

/-- Sign, biased exponent, and fraction of the bits injected by the Wasm harness. -/
theorem input_fields :
    (0x3fdfffffffffffff : ℕ) / 2^63 = 0 ∧
    ((0x3fdfffffffffffff : ℕ) / 2^52) % 2^11 = 1021 ∧
    (0x3fdfffffffffffff : ℕ) % 2^52 = 4503599627370495 := by
  norm_num

/-- Normal binary64 decoding at biased exponent 1021 (unbiased exponent -2). -/
theorem input_value :
    (1 + (4503599627370495 : ℝ) / 2^52) / 4 = x := by
  norm_num [x]

theorem input_in_R1_domain : 0 ≤ x ∧ x ≤ (2147483647 : ℝ) := by
  norm_num [x]

theorem zero_strictly_closer_than_one :
    |x - (0 : ℝ)| < |x - (1 : ℝ)| := by
  norm_num [x, abs_of_nonneg, abs_of_nonpos]

/-- The Wasmtime-observed result 1 violates R1 for this exact input. -/
theorem one_is_not_nearest : ¬ IsNearest x 1 := by
  intro h
  apply not_le_of_gt zero_strictly_closer_than_one
  simpa using h 0

theorem R1_counterexample :
    0 ≤ x ∧ x ≤ (2147483647 : ℝ) ∧ ¬ IsNearest x 1 := by
  exact ⟨input_in_R1_domain.1, input_in_R1_domain.2, one_is_not_nearest⟩

end IRound
