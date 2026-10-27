import Proofs.Spec
import Proofs.Data
import Proofs.Discrepancy

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Proofs

theorem score_certificate : List.Forall₂
    (fun es b => Bounds.good es ∧ b.1 ≤ Bounds.lower es ∧ Bounds.upper es ≤ b.2)
    (Model.samples Counts.blob.data) Data.intervals := by
  rw [Data.es_eq]
  exact .cons Data.bounds0 (.cons Data.bounds1 (.cons Data.bounds2
    (.cons Data.bounds3 (.cons Data.bounds4 (.cons Data.bounds5
      (.cons Data.bounds6 .nil))))))

theorem r1_holds : r1 := by
  apply Bounds.accurate_of_bounds _ _ _ Data.intervals
  · decide +kernel
  · decide +kernel
  · exact score_certificate
  · unfold Bounds.Fits
    decide +kernel

theorem r2_holds : r2 := by
  apply Bounds.accurate_of_bounds _ _ _ Data.intervals
  · decide +kernel
  · decide +kernel
  · exact score_certificate
  · unfold Bounds.Fits
    decide +kernel

end Proofs
