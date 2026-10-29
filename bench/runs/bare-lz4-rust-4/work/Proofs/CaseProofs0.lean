import Proofs.Cases

namespace LZ4Verification

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_0_checked : checkedCase case_0 = true := by decide +kernel

theorem case_1_checked : checkedCase case_1 = true := by decide +kernel

theorem case_2_checked : checkedCase case_2 = true := by decide +kernel

theorem case_3_checked : checkedCase case_3 = true := by decide +kernel

theorem case_4_checked : checkedCase case_4 = true := by decide +kernel

theorem case_5_checked : checkedCase case_5 = true := by decide +kernel

end LZ4Verification
