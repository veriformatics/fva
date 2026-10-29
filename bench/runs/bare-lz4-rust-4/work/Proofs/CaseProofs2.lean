import Proofs.Cases

namespace LZ4Verification

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_12_checked : checkedCase case_12 = true := by decide +kernel

theorem case_13_checked : checkedCase case_13 = true := by decide +kernel

theorem case_14_checked : checkedCase case_14 = true := by decide +kernel

theorem case_15_checked : checkedCase case_15 = true := by decide +kernel

theorem case_16_checked : checkedCase case_16 = true := by decide +kernel

theorem case_17_checked : checkedCase case_17 = true := by decide +kernel

end LZ4Verification
