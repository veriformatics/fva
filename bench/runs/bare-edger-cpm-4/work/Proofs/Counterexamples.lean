import Mathlib

/-! Exact rational certificates for the executable counterexamples.
This is a small arithmetic model, not a formal WebAssembly or R interpreter.
The scripts separately execute the hash-pinned artifact and shipped R code. -/
namespace Verification

-- A strict nearest-rounding certificate for a positive normal binary64.
-- In our examples the mantissa is interior to its binade, so both adjacent
-- representable values have spacing 2^e; strict inequalities avoid tie rules.
def NormalRound (x : ℚ) (m : ℕ) (e : ℤ) : Prop :=
  2^52 < m ∧ m < 2^53 - 1 ∧ -1074 ≤ e ∧ e ≤ 971 ∧
  (m : ℚ) * (2 : ℚ)^e - (2 : ℚ)^e / 2 < x ∧
  x < (m : ℚ) * (2 : ℚ)^e + (2 : ℚ)^e / 2

def rawBoundary : ℚ := 4772185884444444 / 8589934592
def cutoffBoundary : ℚ := 4772185884444445 / 8589934592
def roundedCountOverLibrary : ℚ := 5003999585967218 / 9007199254740992

theorem boundary_raw_round :
    NormalRound ((10 : ℚ) * 1000000 / 18) 4772185884444444 (-33) := by
  norm_num [NormalRound]

theorem boundary_first_cutoff_round :
    NormalRound ((10 : ℚ) / 18) 5003999585967218 (-53) := by
  norm_num [NormalRound]

theorem boundary_second_cutoff_round :
    NormalRound (roundedCountOverLibrary * 1000000) 4772185884444445 (-33) := by
  norm_num [NormalRound, roundedCountOverLibrary]

theorem boundary_disagreement :
    (10 : ℚ) / 18 * 1000000 = 5000000 / 9 ∧
    rawBoundary < cutoffBoundary ∧
    cutoffBoundary - rawBoundary = (2 : ℚ)^(-33 : ℤ) ∧
    |rawBoundary - (10 : ℚ) / 18 * 1000000| = 1 / 19327352832 ∧
    |rawBoundary - (10 : ℚ) / 18 * 1000000| /
      ((10 : ℚ) / 18 * 1000000) = 1 / 10737418240000000 := by
  norm_num [rawBoundary, cutoffBoundary]

-- Exact overflow boundary for round-to-nearest binary64: the midpoint
-- between the largest finite value and the hypothetical next power of two.
def overflowThreshold : ℚ := (2 : ℚ)^1024 - (2 : ℚ)^970

set_option exponentiation.threshold 2048 in
theorem overflow_witness :
    0 < (2 : ℚ)^1023 ∧
    (2 : ℚ)^1023 < overflowThreshold ∧
    overflowThreshold ≤ (2 : ℚ)^1023 * 1000000 ∧
    (2 : ℚ)^1023 / (2 : ℚ)^1023 * 1000000 = 1000000 := by
  norm_num [overflowThreshold]

theorem overflow_target_is_exact_binary64 :
    (8589934592000000 : ℚ) * (2 : ℚ)^(-33 : ℤ) = 1000000 ∧
    NormalRound 1000000 8589934592000000 (-33) := by
  norm_num [NormalRound]

-- A row already reduced to the two tests at the end of filterByExpr.default.
def filterTail (qualifyingSamples required total minTotal : ℚ) : Prop :=
  qualifyingSamples ≥ required - 1 / 10^14 ∧ total ≥ minTotal - 1 / 10^14

theorem total_count_witness :
    (10 : ℚ) / 1000000 * 1000000 = 10 ∧
    (1 : ℚ) ≥ 1 ∧ ¬ filterTail 1 1 10 15 := by
  norm_num [filterTail]

-- Two qualifying samples and total 20 would pass; the actual artifact's
-- lower rounded values mean zero samples qualify at cutoffBoundary.
theorem boundary_filter_witness :
    (10 : ℚ) ≥ 10 ∧ (20 : ℚ) ≥ 15 ∧
    filterTail 2 2 20 15 ∧ ¬ filterTail 0 2 20 15 := by
  norm_num [filterTail]

end Verification

#print axioms Verification.boundary_raw_round
#print axioms Verification.boundary_first_cutoff_round
#print axioms Verification.boundary_second_cutoff_round
#print axioms Verification.boundary_disagreement
#print axioms Verification.overflow_witness
#print axioms Verification.overflow_target_is_exact_binary64
#print axioms Verification.total_count_witness
#print axioms Verification.boundary_filter_witness
