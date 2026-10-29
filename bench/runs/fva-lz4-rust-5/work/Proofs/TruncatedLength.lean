import Proofs.ReplayCore
namespace Proofs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 theorem truncatedLength_holds : truncatedLength := by
  apply replay_checked fresh.1 fresh.2 freshInstance freshSize freshExport freshParams <;> decide +kernel
end Proofs
