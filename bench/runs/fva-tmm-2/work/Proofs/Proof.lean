import Proofs.Spec
import Proofs.Evidence

namespace Proofs

open Model Bounds

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem counts_bytes : Counts.blob.data = matrixText Data.counts := by decide +kernel
theorem edge_bytes : Edge.blob.data = factorText Data.edge := by decide +kernel
theorem rna_bytes : Rna.blob.data = factorText Data.rna := by decide +kernel

theorem R1_holds : R1 := by
  refine ⟨Data.counts, Data.edge, counts_bytes, edge_bytes, ?_, ?_, ?_, ?_, edge_errors⟩
  all_goals decide +kernel

theorem R2_holds : R2 := by
  refine ⟨Data.counts, Data.rna, counts_bytes, rna_bytes, ?_, ?_, ?_, ?_, rna_errors⟩
  all_goals decide +kernel

theorem R3_failure_holds : R3_failure := by
  refine ⟨Data.edge, Data.rna, edge_bytes, rna_bytes, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem R1_tight_failure_holds : R1_tight_failure := by
  refine ⟨Data.counts, Data.edge, counts_bytes, edge_bytes, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · have h := factor_2.1
    have hv : ((Data.edge[2]?.getD (⟨0, []⟩ : Decimal)).value : ℝ) =
        (11253076397204775 / 10000000000000000 : ℚ) := by norm_num [Data.edge, Decimal.value]
    rw [hv, abs_of_neg (by norm_num at h ⊢; linarith)]
    norm_num at h ⊢
    linarith

theorem R2_tight_failure_holds : R2_tight_failure := by
  refine ⟨Data.counts, Data.rna, counts_bytes, rna_bytes, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · have h := factor_2.1
    have hv : ((Data.rna[2]?.getD (⟨0, []⟩ : Decimal)).value : ℝ) =
        (11270795948647565 / 10000000000000000 : ℚ) := by norm_num [Data.rna, Decimal.value]
    rw [hv, abs_of_neg (by norm_num at h ⊢; linarith)]
    norm_num at h ⊢
    linarith

end Proofs
