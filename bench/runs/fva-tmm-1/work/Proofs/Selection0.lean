import Proofs.Ranks0
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace Proofs.Witness
theorem selected0 : selected matrix 0 3 = ps0 := by
  unfold selected
  rw [pairs0]
  dsimp only
  rw [ms_eq0, aa_eq0]
  have h_ms0_keep0 := ms0_keep0
  have h_ms0_keep1 := ms0_keep1
  have h_ms0_keep2 := ms0_keep2
  have h_ms0_keep3 := ms0_keep3
  have h_ms0_keep4 := ms0_keep4
  have h_ms0_keep5 := ms0_keep5
  have h_ms0_keep6 := ms0_keep6
  have h_ms0_keep7 := ms0_keep7
  have h_ms0_keep8 := ms0_keep8
  have h_ms0_keep9 := ms0_keep9
  have h_ms0_keep10 := ms0_keep10
  have h_ms0_keep11 := ms0_keep11
  have h_ms0_keep12 := ms0_keep12
  have h_ms0_keep13 := ms0_keep13
  have h_ms0_keep14 := ms0_keep14
  have h_ms0_keep15 := ms0_keep15
  have h_ms0_keep16 := ms0_keep16
  have h_ms0_keep17 := ms0_keep17
  have h_ms0_keep18 := ms0_keep18
  have h_ms0_keep19 := ms0_keep19
  have h_ms0_keep20 := ms0_keep20
  have h_ms0_keep21 := ms0_keep21
  have h_ms0_keep22 := ms0_keep22
  have h_ms0_keep23 := ms0_keep23
  have h_ms0_keep24 := ms0_keep24
  have h_ms0_keep25 := ms0_keep25
  have h_ms0_keep26 := ms0_keep26
  have h_ms0_keep27 := ms0_keep27
  have h_ms0_keep28 := ms0_keep28
  have h_ms0_keep29 := ms0_keep29
  have h_ms0_keep30 := ms0_keep30
  have h_ms0_keep31 := ms0_keep31
  have h_ms0_keep32 := ms0_keep32
  have h_ms0_keep33 := ms0_keep33
  have h_ms0_keep34 := ms0_keep34
  have h_ms0_keep35 := ms0_keep35
  have h_ms0_keep36 := ms0_keep36
  have h_ms0_keep37 := ms0_keep37
  have h_ms0_keep38 := ms0_keep38
  have h_ms0_keep39 := ms0_keep39
  have h_ms0_keep40 := ms0_keep40
  have h_ms0_keep41 := ms0_keep41
  have h_ms0_keep42 := ms0_keep42
  have h_ms0_keep43 := ms0_keep43
  have h_ms0_keep44 := ms0_keep44
  have h_ms0_keep45 := ms0_keep45
  have h_ms0_keep46 := ms0_keep46
  have h_ms0_keep47 := ms0_keep47
  have h_ms0_keep48 := ms0_keep48
  have h_ms0_keep49 := ms0_keep49
  have h_ms0_keep50 := ms0_keep50
  have h_ms0_keep51 := ms0_keep51
  have h_ms0_keep52 := ms0_keep52
  have h_ms0_keep53 := ms0_keep53
  have h_ms0_keep54 := ms0_keep54
  have h_ms0_keep55 := ms0_keep55
  have h_ms0_keep56 := ms0_keep56
  have h_ms0_keep57 := ms0_keep57
  have h_ms0_keep58 := ms0_keep58
  have h_ms0_keep59 := ms0_keep59
  have h_ms0_keep60 := ms0_keep60
  have h_ms0_keep61 := ms0_keep61
  have h_ms0_keep62 := ms0_keep62
  have h_ms0_keep63 := ms0_keep63
  have h_aa0_keep0 := aa0_keep0
  have h_aa0_keep1 := aa0_keep1
  have h_aa0_keep2 := aa0_keep2
  have h_aa0_keep3 := aa0_keep3
  have h_aa0_keep4 := aa0_keep4
  have h_aa0_keep5 := aa0_keep5
  have h_aa0_keep6 := aa0_keep6
  have h_aa0_keep7 := aa0_keep7
  have h_aa0_keep8 := aa0_keep8
  have h_aa0_keep9 := aa0_keep9
  have h_aa0_keep10 := aa0_keep10
  have h_aa0_keep11 := aa0_keep11
  have h_aa0_keep12 := aa0_keep12
  have h_aa0_keep13 := aa0_keep13
  have h_aa0_keep14 := aa0_keep14
  have h_aa0_keep15 := aa0_keep15
  have h_aa0_keep16 := aa0_keep16
  have h_aa0_keep17 := aa0_keep17
  have h_aa0_keep18 := aa0_keep18
  have h_aa0_keep19 := aa0_keep19
  have h_aa0_keep20 := aa0_keep20
  have h_aa0_keep21 := aa0_keep21
  have h_aa0_keep22 := aa0_keep22
  have h_aa0_keep23 := aa0_keep23
  have h_aa0_keep24 := aa0_keep24
  have h_aa0_keep25 := aa0_keep25
  have h_aa0_keep26 := aa0_keep26
  have h_aa0_keep27 := aa0_keep27
  have h_aa0_keep28 := aa0_keep28
  have h_aa0_keep29 := aa0_keep29
  have h_aa0_keep30 := aa0_keep30
  have h_aa0_keep31 := aa0_keep31
  have h_aa0_keep32 := aa0_keep32
  have h_aa0_keep33 := aa0_keep33
  have h_aa0_keep34 := aa0_keep34
  have h_aa0_keep35 := aa0_keep35
  have h_aa0_keep36 := aa0_keep36
  have h_aa0_keep37 := aa0_keep37
  have h_aa0_keep38 := aa0_keep38
  have h_aa0_keep39 := aa0_keep39
  have h_aa0_keep40 := aa0_keep40
  have h_aa0_keep41 := aa0_keep41
  have h_aa0_keep42 := aa0_keep42
  have h_aa0_keep43 := aa0_keep43
  have h_aa0_keep44 := aa0_keep44
  have h_aa0_keep45 := aa0_keep45
  have h_aa0_keep46 := aa0_keep46
  have h_aa0_keep47 := aa0_keep47
  have h_aa0_keep48 := aa0_keep48
  have h_aa0_keep49 := aa0_keep49
  have h_aa0_keep50 := aa0_keep50
  have h_aa0_keep51 := aa0_keep51
  have h_aa0_keep52 := aa0_keep52
  have h_aa0_keep53 := aa0_keep53
  have h_aa0_keep54 := aa0_keep54
  have h_aa0_keep55 := aa0_keep55
  simp only [div_one] at h_ms0_keep0 h_ms0_keep1 h_ms0_keep2 h_ms0_keep3 h_ms0_keep4 h_ms0_keep5 h_ms0_keep6 h_ms0_keep7 h_ms0_keep8 h_ms0_keep9 h_ms0_keep10 h_ms0_keep11 h_ms0_keep12 h_ms0_keep13 h_ms0_keep14 h_ms0_keep15 h_ms0_keep16 h_ms0_keep17 h_ms0_keep18 h_ms0_keep19 h_ms0_keep20 h_ms0_keep21 h_ms0_keep22 h_ms0_keep23 h_ms0_keep24 h_ms0_keep25 h_ms0_keep26 h_ms0_keep27 h_ms0_keep28 h_ms0_keep29 h_ms0_keep30 h_ms0_keep31 h_ms0_keep32 h_ms0_keep33 h_ms0_keep34 h_ms0_keep35 h_ms0_keep36 h_ms0_keep37 h_ms0_keep38 h_ms0_keep39 h_ms0_keep40 h_ms0_keep41 h_ms0_keep42 h_ms0_keep43 h_ms0_keep44 h_ms0_keep45 h_ms0_keep46 h_ms0_keep47 h_ms0_keep48 h_ms0_keep49 h_ms0_keep50 h_ms0_keep51 h_ms0_keep52 h_ms0_keep53 h_ms0_keep54 h_ms0_keep55 h_ms0_keep56 h_ms0_keep57 h_ms0_keep58 h_ms0_keep59 h_ms0_keep60 h_ms0_keep61 h_ms0_keep62 h_ms0_keep63 h_aa0_keep0 h_aa0_keep1 h_aa0_keep2 h_aa0_keep3 h_aa0_keep4 h_aa0_keep5 h_aa0_keep6 h_aa0_keep7 h_aa0_keep8 h_aa0_keep9 h_aa0_keep10 h_aa0_keep11 h_aa0_keep12 h_aa0_keep13 h_aa0_keep14 h_aa0_keep15 h_aa0_keep16 h_aa0_keep17 h_aa0_keep18 h_aa0_keep19 h_aa0_keep20 h_aa0_keep21 h_aa0_keep22 h_aa0_keep23 h_aa0_keep24 h_aa0_keep25 h_aa0_keep26 h_aa0_keep27 h_aa0_keep28 h_aa0_keep29 h_aa0_keep30 h_aa0_keep31 h_aa0_keep32 h_aa0_keep33 h_aa0_keep34 h_aa0_keep35 h_aa0_keep36 h_aa0_keep37 h_aa0_keep38 h_aa0_keep39 h_aa0_keep40 h_aa0_keep41 h_aa0_keep42 h_aa0_keep43 h_aa0_keep44 h_aa0_keep45 h_aa0_keep46 h_aa0_keep47 h_aa0_keep48 h_aa0_keep49 h_aa0_keep50 h_aa0_keep51 h_aa0_keep52 h_aa0_keep53 h_aa0_keep54 h_aa0_keep55
  norm_num [allps0, ps0, List.filter_cons, List.filter_nil, h_ms0_keep0, h_ms0_keep1, h_ms0_keep2, h_ms0_keep3, h_ms0_keep4, h_ms0_keep5, h_ms0_keep6, h_ms0_keep7, h_ms0_keep8, h_ms0_keep9, h_ms0_keep10, h_ms0_keep11, h_ms0_keep12, h_ms0_keep13, h_ms0_keep14, h_ms0_keep15, h_ms0_keep16, h_ms0_keep17, h_ms0_keep18, h_ms0_keep19, h_ms0_keep20, h_ms0_keep21, h_ms0_keep22, h_ms0_keep23, h_ms0_keep24, h_ms0_keep25, h_ms0_keep26, h_ms0_keep27, h_ms0_keep28, h_ms0_keep29, h_ms0_keep30, h_ms0_keep31, h_ms0_keep32, h_ms0_keep33, h_ms0_keep34, h_ms0_keep35, h_ms0_keep36, h_ms0_keep37, h_ms0_keep38, h_ms0_keep39, h_ms0_keep40, h_ms0_keep41, h_ms0_keep42, h_ms0_keep43, h_ms0_keep44, h_ms0_keep45, h_ms0_keep46, h_ms0_keep47, h_ms0_keep48, h_ms0_keep49, h_ms0_keep50, h_ms0_keep51, h_ms0_keep52, h_ms0_keep53, h_ms0_keep54, h_ms0_keep55, h_ms0_keep56, h_ms0_keep57, h_ms0_keep58, h_ms0_keep59, h_ms0_keep60, h_ms0_keep61, h_ms0_keep62, h_ms0_keep63, h_aa0_keep0, h_aa0_keep1, h_aa0_keep2, h_aa0_keep3, h_aa0_keep4, h_aa0_keep5, h_aa0_keep6, h_aa0_keep7, h_aa0_keep8, h_aa0_keep9, h_aa0_keep10, h_aa0_keep11, h_aa0_keep12, h_aa0_keep13, h_aa0_keep14, h_aa0_keep15, h_aa0_keep16, h_aa0_keep17, h_aa0_keep18, h_aa0_keep19, h_aa0_keep20, h_aa0_keep21, h_aa0_keep22, h_aa0_keep23, h_aa0_keep24, h_aa0_keep25, h_aa0_keep26, h_aa0_keep27, h_aa0_keep28, h_aa0_keep29, h_aa0_keep30, h_aa0_keep31, h_aa0_keep32, h_aa0_keep33, h_aa0_keep34, h_aa0_keep35, h_aa0_keep36, h_aa0_keep37, h_aa0_keep38, h_aa0_keep39, h_aa0_keep40, h_aa0_keep41, h_aa0_keep42, h_aa0_keep43, h_aa0_keep44, h_aa0_keep45, h_aa0_keep46, h_aa0_keep47, h_aa0_keep48, h_aa0_keep49, h_aa0_keep50, h_aa0_keep51, h_aa0_keep52, h_aa0_keep53, h_aa0_keep54, h_aa0_keep55]
end Proofs.Witness
