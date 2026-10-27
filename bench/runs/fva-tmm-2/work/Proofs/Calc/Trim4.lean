import Proofs.Data
import FVA.Lifted

namespace Proofs
open Bounds Model
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem kept_4 : kept Data.counts 4 3 = Data.kept4 := by kernel_rfl

end Proofs
