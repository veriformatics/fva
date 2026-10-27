import Proofs.Data
import FVA.Lifted

namespace Proofs
open Bounds Model
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem kept_1 : kept Data.counts 1 3 = Data.kept1 := by kernel_rfl

end Proofs
