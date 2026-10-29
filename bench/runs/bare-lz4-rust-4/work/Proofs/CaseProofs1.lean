import Proofs.Cases

namespace LZ4Verification

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_6_checked : checkedCase case_6 = true := by decide +kernel

theorem case_7_checked : checkedCase case_7 = true := by decide +kernel

theorem case_8_checked : checkedCase case_8 = true := by decide +kernel

theorem case_9_checked : checkedCase case_9 = true := by decide +kernel

theorem case_10_checked : checkedCase case_10 = true := by decide +kernel

theorem case_11_checked : checkedCase case_11 = true := by decide +kernel

end LZ4Verification
