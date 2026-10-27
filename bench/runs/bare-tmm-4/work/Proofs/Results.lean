import Proofs.Certificates
import Proofs.Artifacts
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Verification
theorem R1_model : ∀ i : Fin 7,
    |factor edgeRaw i - (edgeValues i : ℝ)| ≤ ((1/10^12 : ℚ) : ℝ) := by
  intro i
  fin_cases i
  · exact factor_near edgeRaw edgeLo edgeHi edgeRaw_bounds 0
      log_056 log_057 (edgeValues 0) (1/10^12)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact factor_near edgeRaw edgeLo edgeHi edgeRaw_bounds 1
      log_091 log_092 (edgeValues 1) (1/10^12)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact factor_near edgeRaw edgeLo edgeHi edgeRaw_bounds 2
      log_071 log_072 (edgeValues 2) (1/10^12)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact factor_near edgeRaw edgeLo edgeHi edgeRaw_bounds 3
      log_042 log_043 (edgeValues 3) (1/10^12)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact factor_near edgeRaw edgeLo edgeHi edgeRaw_bounds 4
      log_024 log_025 (edgeValues 4) (1/10^12)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact factor_near edgeRaw edgeLo edgeHi edgeRaw_bounds 5
      log_038 log_039 (edgeValues 5) (1/10^12)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact factor_near edgeRaw edgeLo edgeHi edgeRaw_bounds 6
      log_050 log_051 (edgeValues 6) (1/10^12)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem R2_model : ∀ i : Fin 7,
    |factor rnaRaw i - (rnaValues i : ℝ)| ≤ ((1/10^12 : ℚ) : ℝ) := by
  intro i
  fin_cases i
  · exact factor_near rnaRaw rnaLo rnaHi rnaRaw_bounds 0
      log_054 log_055 (rnaValues 0) (1/10^12)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact factor_near rnaRaw rnaLo rnaHi rnaRaw_bounds 1
      log_093 log_094 (rnaValues 1) (1/10^12)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact factor_near rnaRaw rnaLo rnaHi rnaRaw_bounds 2
      log_074 log_075 (rnaValues 2) (1/10^12)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact factor_near rnaRaw rnaLo rnaHi rnaRaw_bounds 3
      log_045 log_046 (rnaValues 3) (1/10^12)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact factor_near rnaRaw rnaLo rnaHi rnaRaw_bounds 4
      log_026 log_027 (rnaValues 4) (1/10^12)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact factor_near rnaRaw rnaLo rnaHi rnaRaw_bounds 5
      log_040 log_041 (rnaValues 5) (1/10^12)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact factor_near rnaRaw rnaLo rnaHi rnaRaw_bounds 6
      log_052 log_053 (rnaValues 6) (1/10^12)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem R1_selected_TMM : ∀ i : Fin 7,
    |selectedTMM counts edgeMasks i - (edgeValues i : ℝ)| ≤ ((1/10^12 : ℚ) : ℝ) := by
  simpa only [selectedTMM, ← edgeRaw_from_counts] using R1_model
theorem R2_selected_TMM : ∀ i : Fin 7,
    |selectedTMM counts rnaMasks i - (rnaValues i : ℝ)| ≤ ((1/10^12 : ℚ) : ℝ) := by
  simpa only [selectedTMM, ← rnaRaw_from_counts] using R2_model
#print axioms R1_selected_TMM
#print axioms R2_selected_TMM
#print axioms R1_model
#print axioms R2_model
#print axioms R3_gap
#print axioms R3_rounding
end Verification
