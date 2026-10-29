import Mathlib

/- Exact arithmetic for the input supplied to the shipped module by witness.wat.
   Module execution is checked separately by verify.py, not axiomatized here. -/
namespace Counterexample

def inputBits : ℕ := 0x3fdfffffffffffff

def input : ℚ := 1 / 2 - 1 / 2 ^ 54

/-- Sign, biased exponent, and fraction of the binary64 witness. -/
theorem input_fields :
    inputBits / 2 ^ 63 = 0 ∧
    inputBits / 2 ^ 52 % 2048 = 1021 ∧
    inputBits % 2 ^ 52 = 2 ^ 52 - 1 := by
  norm_num [inputBits]

/-- The exponent is neither the zero/subnormal nor infinity/NaN encoding. -/
theorem input_is_normal :
    0 < inputBits / 2 ^ 52 % 2048 ∧
    inputBits / 2 ^ 52 % 2048 < 2047 := by
  norm_num [inputBits]

/-- Standard positive-normal binary64 decoding, evaluated exactly in ℚ. -/
theorem input_decoding :
    input =
      (1 + ((inputBits % 2 ^ 52 : ℕ) : ℚ) / 2 ^ 52) *
        (2 : ℚ) ^ (((inputBits / 2 ^ 52 % 2048 : ℕ) : ℤ) - 1023) := by
  norm_num [input, inputBits]

def Nearest (x : ℚ) (n : ℤ) : Prop :=
  ∀ m : ℤ, |x - (n : ℚ)| ≤ |x - (m : ℚ)|

theorem input_in_range : 0 ≤ input ∧ input ≤ 2147483647 := by
  norm_num [input]

/-- The result observed from Wasmtime is strictly farther away than zero. -/
theorem zero_strictly_closer : |input - (0 : ℚ)| < |input - (1 : ℚ)| := by
  norm_num [input]

theorem one_not_nearest : ¬ Nearest input 1 := by
  intro h
  have h0 := h 0
  exact (not_le_of_gt zero_strictly_closer) h0

/-- Certificate used with the actual execution result of 1. No tie is involved. -/
theorem r1_counterexample :
    (0 ≤ input ∧ input ≤ 2147483647) ∧ ¬ Nearest input 1 :=
  ⟨input_in_range, one_not_nearest⟩

#print axioms r1_counterexample
#print axioms input_decoding

end Counterexample
