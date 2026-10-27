import Proofs.ScoreData
import Proofs.Interpretation

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Proofs

theorem R1_failure_holds : R1_failure := by
  refine ⟨matrix, edgeValues, counts_bytes, edge_bytes, matrix_shape.1,
    matrix_shape.2, rfl, reference_eq, ?_⟩
  have h : (decimalValue (edgeValues[2]?.getD (0,0)) : ℝ) + 1/100 < 114/100 := by
    norm_num [edgeValues, decimalValue]
  exact h.trans factor_lower

theorem R2_failure_holds : R2_failure := by
  refine ⟨matrix, rnaValues, counts_bytes, rna_bytes, matrix_shape.1,
    matrix_shape.2, rfl, reference_eq, ?_⟩
  have h : (decimalValue (rnaValues[2]?.getD (0,0)) : ℝ) + 1/100 < 114/100 := by
    norm_num [rnaValues, decimalValue]
  exact h.trans factor_lower

theorem R3_failure_holds : R3_failure := by
  refine ⟨edgeValues, rnaValues, edge_bytes, rna_bytes, rfl, rfl, ?_⟩
  decide +kernel

end Proofs
