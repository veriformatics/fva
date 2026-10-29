import Mathlib

namespace Verification

def witnessBits : ℕ := 0x3fdfffffffffffff

noncomputable def witness : ℝ := (9007199254740991 : ℝ) / 18014398509481984

-- An integer is nearest if no other integer is strictly closer.
-- This definition permits either result at a tie.
def IsNearest (x : ℝ) (r : ℤ) : Prop :=
  ∀ n : ℤ, |x - (r : ℝ)| ≤ |x - (n : ℝ)|

-- The bit pattern has sign 0, normal biased exponent 1021, and all-one fraction.
theorem witness_fields :
    witnessBits / 2^63 = 0 ∧
    (witnessBits / 2^52) % 2^11 = 1021 ∧
    witnessBits % 2^52 = 4503599627370495 := by
  norm_num [witnessBits]

-- IEEE binary64 decoding for those fields: (1 + fraction / 2^52) * 2^(1021-1023).
theorem witness_decode :
    witness = (1 + (4503599627370495 : ℝ) / 2^52) / 2^2 := by
  norm_num [witness]

theorem witness_below_half :
    witness = (1 : ℝ) / 2 - 1 / 2^54 := by
  norm_num [witness]

-- The actual return value 1 is strictly farther away than the integer 0.
theorem r1_counterexample :
    0 ≤ witness ∧ witness ≤ 2147483647 ∧
    |witness - (0 : ℝ)| < |witness - (1 : ℝ)| ∧
    ¬ IsNearest witness 1 := by
  have h : |witness - (0 : ℝ)| < |witness - (1 : ℝ)| := by
    norm_num [witness, abs_of_pos, abs_of_neg]
  refine ⟨by norm_num [witness], by norm_num [witness], h, ?_⟩
  intro hn
  exact (not_le_of_gt h) (by simpa using hn 0)

#print axioms witness_fields
#print axioms witness_decode
#print axioms witness_below_half
#print axioms r1_counterexample

end Verification
