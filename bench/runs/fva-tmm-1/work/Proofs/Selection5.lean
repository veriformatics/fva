import Proofs.Ranks5
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace Proofs.Witness
theorem selected5 : selected matrix 5 3 = ps5 := by
  unfold selected
  rw [pairs5]
  dsimp only
  rw [ms_eq5, aa_eq5]
  have h_ms5_keep0 := ms5_keep0
  have h_ms5_keep1 := ms5_keep1
  have h_ms5_keep2 := ms5_keep2
  have h_ms5_keep3 := ms5_keep3
  have h_ms5_keep4 := ms5_keep4
  have h_ms5_keep5 := ms5_keep5
  have h_ms5_keep6 := ms5_keep6
  have h_ms5_keep7 := ms5_keep7
  have h_ms5_keep8 := ms5_keep8
  have h_ms5_keep9 := ms5_keep9
  have h_ms5_keep10 := ms5_keep10
  have h_ms5_keep11 := ms5_keep11
  have h_ms5_keep12 := ms5_keep12
  have h_ms5_keep13 := ms5_keep13
  have h_ms5_keep14 := ms5_keep14
  have h_ms5_keep15 := ms5_keep15
  have h_ms5_keep16 := ms5_keep16
  have h_ms5_keep17 := ms5_keep17
  have h_ms5_keep18 := ms5_keep18
  have h_ms5_keep19 := ms5_keep19
  have h_ms5_keep20 := ms5_keep20
  have h_ms5_keep21 := ms5_keep21
  have h_ms5_keep22 := ms5_keep22
  have h_ms5_keep23 := ms5_keep23
  have h_ms5_keep24 := ms5_keep24
  have h_ms5_keep25 := ms5_keep25
  have h_ms5_keep26 := ms5_keep26
  have h_ms5_keep27 := ms5_keep27
  have h_ms5_keep28 := ms5_keep28
  have h_ms5_keep29 := ms5_keep29
  have h_ms5_keep30 := ms5_keep30
  have h_ms5_keep31 := ms5_keep31
  have h_ms5_keep32 := ms5_keep32
  have h_ms5_keep33 := ms5_keep33
  have h_ms5_keep34 := ms5_keep34
  have h_ms5_keep35 := ms5_keep35
  have h_ms5_keep36 := ms5_keep36
  have h_ms5_keep37 := ms5_keep37
  have h_ms5_keep38 := ms5_keep38
  have h_ms5_keep39 := ms5_keep39
  have h_ms5_keep40 := ms5_keep40
  have h_ms5_keep41 := ms5_keep41
  have h_ms5_keep42 := ms5_keep42
  have h_ms5_keep43 := ms5_keep43
  have h_ms5_keep44 := ms5_keep44
  have h_ms5_keep45 := ms5_keep45
  have h_ms5_keep46 := ms5_keep46
  have h_ms5_keep47 := ms5_keep47
  have h_ms5_keep48 := ms5_keep48
  have h_ms5_keep49 := ms5_keep49
  have h_ms5_keep50 := ms5_keep50
  have h_ms5_keep51 := ms5_keep51
  have h_ms5_keep52 := ms5_keep52
  have h_ms5_keep53 := ms5_keep53
  have h_ms5_keep54 := ms5_keep54
  have h_ms5_keep55 := ms5_keep55
  have h_ms5_keep56 := ms5_keep56
  have h_ms5_keep57 := ms5_keep57
  have h_ms5_keep58 := ms5_keep58
  have h_ms5_keep59 := ms5_keep59
  have h_ms5_keep60 := ms5_keep60
  have h_ms5_keep61 := ms5_keep61
  have h_ms5_keep62 := ms5_keep62
  have h_aa5_keep0 := aa5_keep0
  have h_aa5_keep1 := aa5_keep1
  have h_aa5_keep2 := aa5_keep2
  have h_aa5_keep3 := aa5_keep3
  have h_aa5_keep4 := aa5_keep4
  have h_aa5_keep5 := aa5_keep5
  have h_aa5_keep6 := aa5_keep6
  have h_aa5_keep7 := aa5_keep7
  have h_aa5_keep8 := aa5_keep8
  have h_aa5_keep9 := aa5_keep9
  have h_aa5_keep10 := aa5_keep10
  have h_aa5_keep11 := aa5_keep11
  have h_aa5_keep12 := aa5_keep12
  have h_aa5_keep13 := aa5_keep13
  have h_aa5_keep14 := aa5_keep14
  have h_aa5_keep15 := aa5_keep15
  have h_aa5_keep16 := aa5_keep16
  have h_aa5_keep17 := aa5_keep17
  have h_aa5_keep18 := aa5_keep18
  have h_aa5_keep19 := aa5_keep19
  have h_aa5_keep20 := aa5_keep20
  have h_aa5_keep21 := aa5_keep21
  have h_aa5_keep22 := aa5_keep22
  have h_aa5_keep23 := aa5_keep23
  have h_aa5_keep24 := aa5_keep24
  have h_aa5_keep25 := aa5_keep25
  have h_aa5_keep26 := aa5_keep26
  have h_aa5_keep27 := aa5_keep27
  have h_aa5_keep28 := aa5_keep28
  have h_aa5_keep29 := aa5_keep29
  have h_aa5_keep30 := aa5_keep30
  have h_aa5_keep31 := aa5_keep31
  have h_aa5_keep32 := aa5_keep32
  have h_aa5_keep33 := aa5_keep33
  have h_aa5_keep34 := aa5_keep34
  have h_aa5_keep35 := aa5_keep35
  have h_aa5_keep36 := aa5_keep36
  have h_aa5_keep37 := aa5_keep37
  have h_aa5_keep38 := aa5_keep38
  have h_aa5_keep39 := aa5_keep39
  have h_aa5_keep40 := aa5_keep40
  have h_aa5_keep41 := aa5_keep41
  have h_aa5_keep42 := aa5_keep42
  have h_aa5_keep43 := aa5_keep43
  have h_aa5_keep44 := aa5_keep44
  have h_aa5_keep45 := aa5_keep45
  have h_aa5_keep46 := aa5_keep46
  have h_aa5_keep47 := aa5_keep47
  have h_aa5_keep48 := aa5_keep48
  have h_aa5_keep49 := aa5_keep49
  have h_aa5_keep50 := aa5_keep50
  have h_aa5_keep51 := aa5_keep51
  have h_aa5_keep52 := aa5_keep52
  have h_aa5_keep53 := aa5_keep53
  have h_aa5_keep54 := aa5_keep54
  simp only [div_one] at h_ms5_keep0 h_ms5_keep1 h_ms5_keep2 h_ms5_keep3 h_ms5_keep4 h_ms5_keep5 h_ms5_keep6 h_ms5_keep7 h_ms5_keep8 h_ms5_keep9 h_ms5_keep10 h_ms5_keep11 h_ms5_keep12 h_ms5_keep13 h_ms5_keep14 h_ms5_keep15 h_ms5_keep16 h_ms5_keep17 h_ms5_keep18 h_ms5_keep19 h_ms5_keep20 h_ms5_keep21 h_ms5_keep22 h_ms5_keep23 h_ms5_keep24 h_ms5_keep25 h_ms5_keep26 h_ms5_keep27 h_ms5_keep28 h_ms5_keep29 h_ms5_keep30 h_ms5_keep31 h_ms5_keep32 h_ms5_keep33 h_ms5_keep34 h_ms5_keep35 h_ms5_keep36 h_ms5_keep37 h_ms5_keep38 h_ms5_keep39 h_ms5_keep40 h_ms5_keep41 h_ms5_keep42 h_ms5_keep43 h_ms5_keep44 h_ms5_keep45 h_ms5_keep46 h_ms5_keep47 h_ms5_keep48 h_ms5_keep49 h_ms5_keep50 h_ms5_keep51 h_ms5_keep52 h_ms5_keep53 h_ms5_keep54 h_ms5_keep55 h_ms5_keep56 h_ms5_keep57 h_ms5_keep58 h_ms5_keep59 h_ms5_keep60 h_ms5_keep61 h_ms5_keep62 h_aa5_keep0 h_aa5_keep1 h_aa5_keep2 h_aa5_keep3 h_aa5_keep4 h_aa5_keep5 h_aa5_keep6 h_aa5_keep7 h_aa5_keep8 h_aa5_keep9 h_aa5_keep10 h_aa5_keep11 h_aa5_keep12 h_aa5_keep13 h_aa5_keep14 h_aa5_keep15 h_aa5_keep16 h_aa5_keep17 h_aa5_keep18 h_aa5_keep19 h_aa5_keep20 h_aa5_keep21 h_aa5_keep22 h_aa5_keep23 h_aa5_keep24 h_aa5_keep25 h_aa5_keep26 h_aa5_keep27 h_aa5_keep28 h_aa5_keep29 h_aa5_keep30 h_aa5_keep31 h_aa5_keep32 h_aa5_keep33 h_aa5_keep34 h_aa5_keep35 h_aa5_keep36 h_aa5_keep37 h_aa5_keep38 h_aa5_keep39 h_aa5_keep40 h_aa5_keep41 h_aa5_keep42 h_aa5_keep43 h_aa5_keep44 h_aa5_keep45 h_aa5_keep46 h_aa5_keep47 h_aa5_keep48 h_aa5_keep49 h_aa5_keep50 h_aa5_keep51 h_aa5_keep52 h_aa5_keep53 h_aa5_keep54
  norm_num [allps5, ps5, List.filter_cons, List.filter_nil, h_ms5_keep0, h_ms5_keep1, h_ms5_keep2, h_ms5_keep3, h_ms5_keep4, h_ms5_keep5, h_ms5_keep6, h_ms5_keep7, h_ms5_keep8, h_ms5_keep9, h_ms5_keep10, h_ms5_keep11, h_ms5_keep12, h_ms5_keep13, h_ms5_keep14, h_ms5_keep15, h_ms5_keep16, h_ms5_keep17, h_ms5_keep18, h_ms5_keep19, h_ms5_keep20, h_ms5_keep21, h_ms5_keep22, h_ms5_keep23, h_ms5_keep24, h_ms5_keep25, h_ms5_keep26, h_ms5_keep27, h_ms5_keep28, h_ms5_keep29, h_ms5_keep30, h_ms5_keep31, h_ms5_keep32, h_ms5_keep33, h_ms5_keep34, h_ms5_keep35, h_ms5_keep36, h_ms5_keep37, h_ms5_keep38, h_ms5_keep39, h_ms5_keep40, h_ms5_keep41, h_ms5_keep42, h_ms5_keep43, h_ms5_keep44, h_ms5_keep45, h_ms5_keep46, h_ms5_keep47, h_ms5_keep48, h_ms5_keep49, h_ms5_keep50, h_ms5_keep51, h_ms5_keep52, h_ms5_keep53, h_ms5_keep54, h_ms5_keep55, h_ms5_keep56, h_ms5_keep57, h_ms5_keep58, h_ms5_keep59, h_ms5_keep60, h_ms5_keep61, h_ms5_keep62, h_aa5_keep0, h_aa5_keep1, h_aa5_keep2, h_aa5_keep3, h_aa5_keep4, h_aa5_keep5, h_aa5_keep6, h_aa5_keep7, h_aa5_keep8, h_aa5_keep9, h_aa5_keep10, h_aa5_keep11, h_aa5_keep12, h_aa5_keep13, h_aa5_keep14, h_aa5_keep15, h_aa5_keep16, h_aa5_keep17, h_aa5_keep18, h_aa5_keep19, h_aa5_keep20, h_aa5_keep21, h_aa5_keep22, h_aa5_keep23, h_aa5_keep24, h_aa5_keep25, h_aa5_keep26, h_aa5_keep27, h_aa5_keep28, h_aa5_keep29, h_aa5_keep30, h_aa5_keep31, h_aa5_keep32, h_aa5_keep33, h_aa5_keep34, h_aa5_keep35, h_aa5_keep36, h_aa5_keep37, h_aa5_keep38, h_aa5_keep39, h_aa5_keep40, h_aa5_keep41, h_aa5_keep42, h_aa5_keep43, h_aa5_keep44, h_aa5_keep45, h_aa5_keep46, h_aa5_keep47, h_aa5_keep48, h_aa5_keep49, h_aa5_keep50, h_aa5_keep51, h_aa5_keep52, h_aa5_keep53, h_aa5_keep54]
end Proofs.Witness
