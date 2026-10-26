import Mathlib.Tactic.NormNum
set_option exponentiation.threshold 2048

/- Exact arithmetic certificates accompanying the *execution* witnesses.
   These definitions are specifications, not a formalization of Wasm or R.
   No Float/native_decide oracle is used by these proofs. -/
namespace Verification

def count : ℚ := 2 ^ 1020
def maxFinite : ℚ := (2 - 1 / 2^52) * 2^1023
def overflowMidpoint : ℚ := 2^1024 - 2^970

-- Both inputs are positive finite binary64 values (a power of two).
theorem r1_inputs : 0 < count ∧ count ≤ maxFinite := by
  norm_num [count, maxFinite]

-- The exact answer is the representable integer 1000000: no final error needed.
theorem r1_exact : count / count * 1000000 = 1000000 := by
  norm_num [count]

-- Multiplication first exceeds even the round-to-nearest overflow midpoint.
theorem r1_intermediate_overflow :
    overflowMidpoint < count * 1000000 := by
  norm_num [overflowMidpoint, count]

-- This is a binary64 normal representation: 53-bit integer significand,
-- multiplied by 2^-33. Its exponent is within the normal exponent range.
theorem r1_target_representable :
    (1000000 : ℚ) = 8589934592000000 / 2^33 ∧
    2^52 ≤ (8589934592000000 : ℕ) ∧
    (8589934592000000 : ℕ) < 2^53 := by
  norm_num

-- Ordinary integer-count witness with default parameters: both columns total 18.
-- The first gene has counts [10,10] and total 20.
def actualCPM : ℚ := 1193046471111111 / 2^31
def divisionResult : ℚ := 2501999792983609 / 2^52
def actualCutoff : ℚ := 4772185884444445 / 2^33

-- Strict nearest-rounding cells; no tie-breaking assumptions are needed here.
def inRoundingCell (exact rounded spacing : ℚ) : Prop :=
  rounded - spacing/2 < exact ∧ exact < rounded + spacing/2

theorem r2_rounding_cells :
    inRoundingCell (10*1000000/18) actualCPM (1/2^33) ∧
    inRoundingCell (10/18) divisionResult (1/2^53) ∧
    inRoundingCell (divisionResult*1000000) actualCutoff (1/2^33) := by
  norm_num [inRoundingCell, actualCPM, divisionResult, actualCutoff]

theorem r2_integer_witness :
    (10 : ℚ) / 18 * 1000000 = 5000000/9 ∧
    (10 : ℚ) ≥ 10 ∧ (10+10 : ℚ) ≥ 15 ∧
    actualCPM < actualCutoff ∧
    actualCutoff - actualCPM = 1/2^33 := by
  norm_num [actualCPM, actualCutoff]

-- Unit library sizes of 1e6 make both the CPMs and min.count cutoff exact.
-- The README's expression-only iff omits the documented total-count veto.
theorem r2_total_veto :
    (10 : ℚ) / 1000000 * 1000000 = 10 ∧
    (1 : ℚ) ≥ 1 ∧ ¬ ((10 : ℚ) ≥ 15 - 1/10^14) := by
  norm_num

-- Values of the actual binary64 inputs and subtraction in the second witness.
def required : ℚ := 1 + 1 / 2^50
def tolerance : ℚ := 6338253001141147 / 2^99
def roundedThreshold : ℚ := 4503599627370455 / 2^52

-- Exact documented sample condition fails; the tolerance condition succeeds.
theorem r2_sample_gap :
    (1 : ℚ) < required ∧
    required - tolerance < 1 ∧
    roundedThreshold ≤ 1 ∧
    (20 : ℚ) ≥ 15 := by
  norm_num [required, tolerance, roundedThreshold]

-- Per-sample condition in the second witness, including the nonqualifying zero.
theorem r2_cpms :
    (20 : ℚ) * 1000000 / 1000000 = 20 ∧
    (0 : ℚ) * 1000000 / 1000000 = 0 ∧
    (10 : ℚ) / 1000000 * 1000000 = 10 ∧
    (20 : ℚ) ≥ 10 ∧ ¬ ((0 : ℚ) ≥ 10) := by
  norm_num

end Verification

#print axioms Verification.r1_inputs
#print axioms Verification.r1_exact
#print axioms Verification.r1_intermediate_overflow
#print axioms Verification.r1_target_representable
#print axioms Verification.r2_rounding_cells
#print axioms Verification.r2_integer_witness
#print axioms Verification.r2_total_veto
#print axioms Verification.r2_sample_gap
#print axioms Verification.r2_cpms
