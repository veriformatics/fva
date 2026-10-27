import Proofs.Data
import FVA.Lifted

namespace Proofs
open Bounds Model
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem kept_2 : kept Data.counts 2 3 = Data.kept2 := by kernel_rfl

end Proofs
