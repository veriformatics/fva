import Proofs.Ranks1
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace Proofs.Witness
theorem selected1 : selected matrix 1 3 = ps1 := by
  unfold selected
  rw [pairs1]
  dsimp only
  rw [ms_eq1, aa_eq1]
  have h_ms1_keep0 := ms1_keep0
  have h_ms1_keep1 := ms1_keep1
  have h_ms1_keep2 := ms1_keep2
  have h_ms1_keep3 := ms1_keep3
  have h_ms1_keep4 := ms1_keep4
  have h_ms1_keep5 := ms1_keep5
  have h_ms1_keep6 := ms1_keep6
  have h_ms1_keep7 := ms1_keep7
  have h_ms1_keep8 := ms1_keep8
  have h_ms1_keep9 := ms1_keep9
  have h_ms1_keep10 := ms1_keep10
  have h_ms1_keep11 := ms1_keep11
  have h_ms1_keep12 := ms1_keep12
  have h_ms1_keep13 := ms1_keep13
  have h_ms1_keep14 := ms1_keep14
  have h_ms1_keep15 := ms1_keep15
  have h_ms1_keep16 := ms1_keep16
  have h_ms1_keep17 := ms1_keep17
  have h_ms1_keep18 := ms1_keep18
  have h_ms1_keep19 := ms1_keep19
  have h_ms1_keep20 := ms1_keep20
  have h_ms1_keep21 := ms1_keep21
  have h_ms1_keep22 := ms1_keep22
  have h_ms1_keep23 := ms1_keep23
  have h_ms1_keep24 := ms1_keep24
  have h_ms1_keep25 := ms1_keep25
  have h_ms1_keep26 := ms1_keep26
  have h_ms1_keep27 := ms1_keep27
  have h_ms1_keep28 := ms1_keep28
  have h_ms1_keep29 := ms1_keep29
  have h_ms1_keep30 := ms1_keep30
  have h_ms1_keep31 := ms1_keep31
  have h_ms1_keep32 := ms1_keep32
  have h_ms1_keep33 := ms1_keep33
  have h_ms1_keep34 := ms1_keep34
  have h_ms1_keep35 := ms1_keep35
  have h_ms1_keep36 := ms1_keep36
  have h_ms1_keep37 := ms1_keep37
  have h_ms1_keep38 := ms1_keep38
  have h_ms1_keep39 := ms1_keep39
  have h_ms1_keep40 := ms1_keep40
  have h_ms1_keep41 := ms1_keep41
  have h_ms1_keep42 := ms1_keep42
  have h_ms1_keep43 := ms1_keep43
  have h_ms1_keep44 := ms1_keep44
  have h_ms1_keep45 := ms1_keep45
  have h_ms1_keep46 := ms1_keep46
  have h_aa1_keep0 := aa1_keep0
  have h_aa1_keep1 := aa1_keep1
  have h_aa1_keep2 := aa1_keep2
  have h_aa1_keep3 := aa1_keep3
  have h_aa1_keep4 := aa1_keep4
  have h_aa1_keep5 := aa1_keep5
  have h_aa1_keep6 := aa1_keep6
  have h_aa1_keep7 := aa1_keep7
  have h_aa1_keep8 := aa1_keep8
  have h_aa1_keep9 := aa1_keep9
  have h_aa1_keep10 := aa1_keep10
  have h_aa1_keep11 := aa1_keep11
  have h_aa1_keep12 := aa1_keep12
  have h_aa1_keep13 := aa1_keep13
  have h_aa1_keep14 := aa1_keep14
  have h_aa1_keep15 := aa1_keep15
  have h_aa1_keep16 := aa1_keep16
  have h_aa1_keep17 := aa1_keep17
  have h_aa1_keep18 := aa1_keep18
  have h_aa1_keep19 := aa1_keep19
  have h_aa1_keep20 := aa1_keep20
  have h_aa1_keep21 := aa1_keep21
  have h_aa1_keep22 := aa1_keep22
  have h_aa1_keep23 := aa1_keep23
  have h_aa1_keep24 := aa1_keep24
  have h_aa1_keep25 := aa1_keep25
  have h_aa1_keep26 := aa1_keep26
  have h_aa1_keep27 := aa1_keep27
  have h_aa1_keep28 := aa1_keep28
  have h_aa1_keep29 := aa1_keep29
  have h_aa1_keep30 := aa1_keep30
  have h_aa1_keep31 := aa1_keep31
  have h_aa1_keep32 := aa1_keep32
  have h_aa1_keep33 := aa1_keep33
  have h_aa1_keep34 := aa1_keep34
  have h_aa1_keep35 := aa1_keep35
  have h_aa1_keep36 := aa1_keep36
  simp only [div_one] at h_ms1_keep0 h_ms1_keep1 h_ms1_keep2 h_ms1_keep3 h_ms1_keep4 h_ms1_keep5 h_ms1_keep6 h_ms1_keep7 h_ms1_keep8 h_ms1_keep9 h_ms1_keep10 h_ms1_keep11 h_ms1_keep12 h_ms1_keep13 h_ms1_keep14 h_ms1_keep15 h_ms1_keep16 h_ms1_keep17 h_ms1_keep18 h_ms1_keep19 h_ms1_keep20 h_ms1_keep21 h_ms1_keep22 h_ms1_keep23 h_ms1_keep24 h_ms1_keep25 h_ms1_keep26 h_ms1_keep27 h_ms1_keep28 h_ms1_keep29 h_ms1_keep30 h_ms1_keep31 h_ms1_keep32 h_ms1_keep33 h_ms1_keep34 h_ms1_keep35 h_ms1_keep36 h_ms1_keep37 h_ms1_keep38 h_ms1_keep39 h_ms1_keep40 h_ms1_keep41 h_ms1_keep42 h_ms1_keep43 h_ms1_keep44 h_ms1_keep45 h_ms1_keep46 h_aa1_keep0 h_aa1_keep1 h_aa1_keep2 h_aa1_keep3 h_aa1_keep4 h_aa1_keep5 h_aa1_keep6 h_aa1_keep7 h_aa1_keep8 h_aa1_keep9 h_aa1_keep10 h_aa1_keep11 h_aa1_keep12 h_aa1_keep13 h_aa1_keep14 h_aa1_keep15 h_aa1_keep16 h_aa1_keep17 h_aa1_keep18 h_aa1_keep19 h_aa1_keep20 h_aa1_keep21 h_aa1_keep22 h_aa1_keep23 h_aa1_keep24 h_aa1_keep25 h_aa1_keep26 h_aa1_keep27 h_aa1_keep28 h_aa1_keep29 h_aa1_keep30 h_aa1_keep31 h_aa1_keep32 h_aa1_keep33 h_aa1_keep34 h_aa1_keep35 h_aa1_keep36
  norm_num [allps1, ps1, List.filter_cons, List.filter_nil, h_ms1_keep0, h_ms1_keep1, h_ms1_keep2, h_ms1_keep3, h_ms1_keep4, h_ms1_keep5, h_ms1_keep6, h_ms1_keep7, h_ms1_keep8, h_ms1_keep9, h_ms1_keep10, h_ms1_keep11, h_ms1_keep12, h_ms1_keep13, h_ms1_keep14, h_ms1_keep15, h_ms1_keep16, h_ms1_keep17, h_ms1_keep18, h_ms1_keep19, h_ms1_keep20, h_ms1_keep21, h_ms1_keep22, h_ms1_keep23, h_ms1_keep24, h_ms1_keep25, h_ms1_keep26, h_ms1_keep27, h_ms1_keep28, h_ms1_keep29, h_ms1_keep30, h_ms1_keep31, h_ms1_keep32, h_ms1_keep33, h_ms1_keep34, h_ms1_keep35, h_ms1_keep36, h_ms1_keep37, h_ms1_keep38, h_ms1_keep39, h_ms1_keep40, h_ms1_keep41, h_ms1_keep42, h_ms1_keep43, h_ms1_keep44, h_ms1_keep45, h_ms1_keep46, h_aa1_keep0, h_aa1_keep1, h_aa1_keep2, h_aa1_keep3, h_aa1_keep4, h_aa1_keep5, h_aa1_keep6, h_aa1_keep7, h_aa1_keep8, h_aa1_keep9, h_aa1_keep10, h_aa1_keep11, h_aa1_keep12, h_aa1_keep13, h_aa1_keep14, h_aa1_keep15, h_aa1_keep16, h_aa1_keep17, h_aa1_keep18, h_aa1_keep19, h_aa1_keep20, h_aa1_keep21, h_aa1_keep22, h_aa1_keep23, h_aa1_keep24, h_aa1_keep25, h_aa1_keep26, h_aa1_keep27, h_aa1_keep28, h_aa1_keep29, h_aa1_keep30, h_aa1_keep31, h_aa1_keep32, h_aa1_keep33, h_aa1_keep34, h_aa1_keep35, h_aa1_keep36]
end Proofs.Witness
