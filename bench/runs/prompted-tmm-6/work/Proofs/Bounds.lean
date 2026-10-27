import Proofs.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Verification

theorem log_root_upper (x u : ℝ) (hx : 0 < x) (hu : 0 < u)
    (h : x ≤ u^8) : Real.log x ≤ 8 * (u - 1) := by
  calc
    Real.log x ≤ Real.log (u^8) := Real.log_le_log hx h
    _ = 8 * Real.log u := by rw [Real.log_pow]; norm_num
    _ ≤ 8 * (u - 1) := by linarith [Real.log_le_sub_one_of_pos hu]

theorem logMean_upper : logMean < 3 / 125 := by
  have h2_2 : Real.log ((2194 : ℝ) / 2522) ≤ 8 * ((982736 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h3_2 : Real.log ((3291 : ℝ) / 2522) ≤ 8 * ((1033827 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h3_3 : Real.log ((3291 : ℝ) / 3783) ≤ 8 * ((982736 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h4_3 : Real.log ((4388 : ℝ) / 3783) ≤ 8 * ((1018718 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h4_4 : Real.log ((4388 : ℝ) / 5044) ≤ 8 * ((982736 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h4_5 : Real.log ((4388 : ℝ) / 6305) ≤ 8 * ((955703 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h5_3 : Real.log ((5485 : ℝ) / 3783) ≤ 8 * ((1047533 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h5_4 : Real.log ((5485 : ℝ) / 5044) ≤ 8 * ((1010533 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h5_5 : Real.log ((5485 : ℝ) / 6305) ≤ 8 * ((982736 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h5_6 : Real.log ((5485 : ℝ) / 7566) ≤ 8 * ((960592 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h6_4 : Real.log ((6582 : ℝ) / 5044) ≤ 8 * ((1033827 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h6_5 : Real.log ((6582 : ℝ) / 6305) ≤ 8 * ((1005389 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h6_6 : Real.log ((6582 : ℝ) / 7566) ≤ 8 * ((982736 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h6_7 : Real.log ((6582 : ℝ) / 8827) ≤ 8 * ((963981 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h7_4 : Real.log ((7679 : ℝ) / 5044) ≤ 8 * ((1053941 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h7_5 : Real.log ((7679 : ℝ) / 6305) ≤ 8 * ((1024950 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h8_5 : Real.log ((8776 : ℝ) / 6305) ≤ 8 * ((1042201 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h8_9 : Real.log ((8776 : ℝ) / 11349) ≤ 8 * ((968373 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h8_10 : Real.log ((8776 : ℝ) / 12610) ≤ 8 * ((955703 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h9_6 : Real.log ((9873 : ℝ) / 7566) ≤ 8 * ((1033827 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h9_7 : Real.log ((9873 : ℝ) / 8827) ≤ 8 * ((1014098 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h10_6 : Real.log ((10970 : ℝ) / 7566) ≤ 8 * ((1047533 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h10_9 : Real.log ((10970 : ℝ) / 11349) ≤ 8 * ((995764 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  have h12_8 : Real.log ((13164 : ℝ) / 10088) ≤ 8 * ((1033827 : ℝ) / 1000000 - 1) := by
    apply log_root_upper
    all_goals norm_num
  unfold logMean
  norm_num [retained_eq, weight, ratio, reference_eq, lib0, lib3]
  linarith

theorem rawFirst_upper : rawFirst < 41 / 40 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 41 / 40)
  have ltlog : logMean < Real.log (41 / 40) := by
    have := logMean_upper
    norm_num at h
    linarith
  exact (Real.lt_log_iff_exp_lt (by norm_num)).1 ltlog

end Verification
