import Mathlib

/- Exact mathematics for the input exercised by check_counterexample.py.
   Execution of the shipped Wasm is checked separately by that script. -/
namespace Counterexample

noncomputable def input : ℝ := 9007199254740991 / 18014398509481984

def IsNearest (x : ℝ) (n : ℤ) : Prop :=
  ∀ m : ℤ, |x - (n : ℝ)| ≤ |x - (m : ℝ)|

-- The sign, exponent, and fraction of binary64 bits 0x3fdfffffffffffff.
theorem input_binary64_value :
    input = (1 + (4503599627370495 : ℝ) / 4503599627370496) / 4 := by
  norm_num [input]

theorem input_in_domain : 0 ≤ input ∧ input ≤ 2147483647 := by
  norm_num [input]

theorem zero_strictly_nearer_than_one :
    |input - (0 : ℝ)| < |input - (1 : ℝ)| := by
  norm_num [input, abs_of_nonneg, abs_of_nonpos]

theorem zero_unique_nearest (n : ℤ) (hn : n ≠ 0) :
    |input - (0 : ℝ)| < |input - (n : ℝ)| := by
  have hx : 0 < input ∧ input < 1 / 2 := by norm_num [input]
  rcases lt_or_gt_of_ne hn with hn | hn
  · have hni : n ≤ -1 := by omega
    have hnr : (n : ℝ) ≤ -1 := by exact_mod_cast hni
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · have hni : 1 ≤ n := by omega
    have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hni
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith

theorem zero_is_nearest : IsNearest input 0 := by
  intro n
  by_cases hn : n = 0
  · subst n; exact le_rfl
  · simpa only [Int.cast_zero] using (zero_unique_nearest n hn).le

theorem one_not_nearest : ¬ IsNearest input 1 := by
  intro h
  have h0 := h 0
  have hstrict := zero_strictly_nearer_than_one
  norm_num only [Int.cast_zero, Int.cast_one] at h0
  linarith

-- The returned value 1 is measured by the artifact execution, not assumed
-- to follow from a formalized Wasm interpreter.
theorem r1_counterexample :
    0 ≤ input ∧ input ≤ 2147483647 ∧ ¬ IsNearest input 1 :=
  ⟨input_in_domain.1, input_in_domain.2, one_not_nearest⟩

end Counterexample

#print axioms Counterexample.input_binary64_value
#print axioms Counterexample.zero_is_nearest
#print axioms Counterexample.r1_counterexample
