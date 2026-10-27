import Proofs.LogBounds
import Proofs.SelfComparison
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Proofs.Numeric

theorem raw3 : ((-1 / 10000000) : ℝ) ≤ rawLog Witness.matrix 3 3 ∧
    rawLog Witness.matrix 3 3 ≤ ((1 / 10000000) : ℝ) := by
  rw [raw3_zero]
  constructor <;> norm_num
end Proofs.Numeric
