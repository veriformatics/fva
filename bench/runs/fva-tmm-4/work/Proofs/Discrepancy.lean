import Proofs.Spec
import Mathlib.Tactic

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Proofs

theorem r3_failure_holds : r3_failure := by
  unfold r3_failure FVA.Cert.Accepted Model.Agree
  decide +kernel

theorem r3_witness_holds : r3_witness := by
  unfold r3_witness
  decide +kernel

end Proofs
