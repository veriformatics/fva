import Proofs.Data
import FVA.Lifted

namespace Proofs
open Bounds Model
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem kept_0 : kept Data.counts 0 3 = Data.kept0 := by kernel_rfl

end Proofs
