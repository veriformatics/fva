import Mathlib

set_option exponentiation.threshold 2048

/-!
Exact arithmetic certificates for the witnesses executed by verification/check.py.
These definitions do not purport to formalize Wasm or R. Artifact execution and
the concrete R bridge are checked separately by that script.
-/
namespace EdgeRVerification

def idealCPM (c L : ℚ) : ℚ := c / L * 1000000

-- Decode the positive, normal binary64 values used here. The predicates in
-- r2_encodings establish that the inputs fall in that domain.
def positiveNormalValue (bits : ℕ) : ℚ :=
  ((2^52 + bits % 2^52 : ℕ) : ℚ) *
    (2 : ℚ) ^ (((bits / 2^52) % 2048 : ℕ) : ℤ) / (2 : ℚ)^1075

def actualCPM : ℚ := 5629448869173297 / 562949953421312
def cutoffDivision : ℚ := 1475726244360565 / 147573952589676412928
def cutoffCPM : ℚ := 2814724434586649 / 281474976710656
def ulpAtTen : ℚ := 1 / 2^49

-- A strict midpoint certificate: no tie-breaking convention is needed.
def insideRoundingCell (exact rounded spacing : ℚ) : Prop :=
  rounded - spacing / 2 < exact ∧ exact < rounded + spacing / 2

theorem r1_positive_input : (0 : ℚ) < 2^1020 := by norm_num

theorem r1_ideal : idealCPM (2^1020) (2^1020) = 1000000 := by
  norm_num [idealCPM]

-- IEEE binary64 round-to-nearest overflow midpoint. The exact first
-- multiplication lies beyond it; Wasmtime checks the actual +infinity result.
theorem r1_intermediate_exceeds_overflow_midpoint :
    (2 : ℚ)^1024 - (2 : ℚ)^970 < (2 : ℚ)^1020 * 1000000 := by
  norm_num

theorem r2_encodings :
    positiveNormalValue 0x4023fff43420d831 = actualCPM ∧
    positiveNormalValue 0x4023fff43420d832 = cutoffCPM ∧
    positiveNormalValue 0x3ee4f8a92a52c5d4 = cutoffDivision ∧
    0x4023fff43420d831 / 2^63 = 0 ∧
    0x4023fff43420d831 / 2^52 % 2048 = 1026 ∧
    0x4023fff43420d832 / 2^63 = 0 ∧
    0x4023fff43420d832 / 2^52 % 2048 = 1026 ∧
    0x3ee4f8a92a52c5d4 / 2^63 = 0 ∧
    0x3ee4f8a92a52c5d4 / 2^52 % 2048 = 1006 := by
  norm_num [positiveNormalValue, actualCPM, cutoffCPM, cutoffDivision]

theorem r2_rounding_cells :
    insideRoundingCell ((10 : ℚ) * 1000000 / 1000009) actualCPM ulpAtTen ∧
    insideRoundingCell ((10 : ℚ) / 1000009) cutoffDivision (1 / 2^69) ∧
    insideRoundingCell (cutoffDivision * 1000000) cutoffCPM ulpAtTen := by
  norm_num [insideRoundingCell, actualCPM, cutoffDivision, cutoffCPM, ulpAtTen]

theorem r2_one_ulp_gap : cutoffCPM - actualCPM = ulpAtTen := by
  norm_num [cutoffCPM, actualCPM, ulpAtTen]

-- Specialize the source's two final tests to the one-row/two-column witness.
def boundaryKeep : Prop :=
  (if actualCPM ≥ cutoffCPM then (2 : ℚ) else 0) ≥ 2 - 1/10^14 ∧
  (20 : ℚ) ≥ 15 - 1/10^14

-- Equal libraries imply median = L, so each scaled minimum count is 10.
def boundaryDocumented : Prop :=
  (10 : ℚ) ≥ 10 * 1000009 / 1000009 ∧
  (2 : ℚ) ≥ 2 ∧ (20 : ℚ) ≥ 15

theorem r2_boundary_counterexample : boundaryDocumented ∧ ¬ boundaryKeep := by
  norm_num [boundaryDocumented, boundaryKeep, actualCPM, cutoffCPM]

theorem r2_literal_iff_counterexample :
    (10 : ℚ) ≥ 10 ∧ (1 : ℚ) ≥ 1 - 1/10^14 ∧
    ¬ ((10 : ℚ) ≥ 15 - 1/10^14) := by norm_num

end EdgeRVerification
