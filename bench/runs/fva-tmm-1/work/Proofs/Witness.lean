import Proofs.Selection0
import Proofs.Selection1
import Proofs.Selection2
import Proofs.Selection3
import Proofs.Selection4
import Proofs.Selection5
import Proofs.Selection6
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Proofs.Witness
theorem matrix_ok : matrixOK matrix := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ref_ok, ?_⟩
  intro j hj
  simp only [List.mem_range] at hj
  interval_cases j
  · rw [selected0, lib0, lib3]; decide +kernel
  · rw [selected1, lib1, lib3]; decide +kernel
  · rw [selected2, lib2, lib3]; decide +kernel
  · rw [selected3, lib3]; decide +kernel
  · rw [selected4, lib4, lib3]; decide +kernel
  · rw [selected5, lib5, lib3]; decide +kernel
  · rw [selected6, lib6, lib3]; decide +kernel
end Proofs.Witness
