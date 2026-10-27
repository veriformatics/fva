import Proofs.Data
import FVA.Lifted

namespace Proofs
open Bounds Model
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem kept_5 : kept Data.counts 5 3 = Data.kept5 := by kernel_rfl

end Proofs
