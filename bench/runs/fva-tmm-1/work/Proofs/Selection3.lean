import Proofs.Ranks3
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace Proofs.Witness
theorem selected3 : selected matrix 3 3 = ps3 := by
  unfold selected
  rw [pairs3]
  dsimp only
  rw [ms_eq3, aa_eq3]
  have h_ms3_keep0 := ms3_keep0
  have h_aa3_keep0 := aa3_keep0
  have h_aa3_keep1 := aa3_keep1
  have h_aa3_keep2 := aa3_keep2
  have h_aa3_keep3 := aa3_keep3
  have h_aa3_keep4 := aa3_keep4
  have h_aa3_keep5 := aa3_keep5
  have h_aa3_keep6 := aa3_keep6
  have h_aa3_keep7 := aa3_keep7
  have h_aa3_keep8 := aa3_keep8
  have h_aa3_keep9 := aa3_keep9
  have h_aa3_keep10 := aa3_keep10
  have h_aa3_keep11 := aa3_keep11
  have h_aa3_keep12 := aa3_keep12
  have h_aa3_keep13 := aa3_keep13
  have h_aa3_keep14 := aa3_keep14
  have h_aa3_keep15 := aa3_keep15
  have h_aa3_keep16 := aa3_keep16
  have h_aa3_keep17 := aa3_keep17
  have h_aa3_keep18 := aa3_keep18
  simp only [div_one] at h_ms3_keep0 h_aa3_keep0 h_aa3_keep1 h_aa3_keep2 h_aa3_keep3 h_aa3_keep4 h_aa3_keep5 h_aa3_keep6 h_aa3_keep7 h_aa3_keep8 h_aa3_keep9 h_aa3_keep10 h_aa3_keep11 h_aa3_keep12 h_aa3_keep13 h_aa3_keep14 h_aa3_keep15 h_aa3_keep16 h_aa3_keep17 h_aa3_keep18
  norm_num [allps3, ps3, List.filter_cons, List.filter_nil, h_ms3_keep0, h_aa3_keep0, h_aa3_keep1, h_aa3_keep2, h_aa3_keep3, h_aa3_keep4, h_aa3_keep5, h_aa3_keep6, h_aa3_keep7, h_aa3_keep8, h_aa3_keep9, h_aa3_keep10, h_aa3_keep11, h_aa3_keep12, h_aa3_keep13, h_aa3_keep14, h_aa3_keep15, h_aa3_keep16, h_aa3_keep17, h_aa3_keep18]
end Proofs.Witness
