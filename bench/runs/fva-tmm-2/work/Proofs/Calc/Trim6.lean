import Proofs.Data
import FVA.Lifted

namespace Proofs
open Bounds Model
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem kept_6 : kept Data.counts 6 3 = Data.kept6 := by kernel_rfl

end Proofs
