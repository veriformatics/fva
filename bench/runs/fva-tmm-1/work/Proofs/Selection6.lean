import Proofs.Ranks6
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace Proofs.Witness
theorem selected6 : selected matrix 6 3 = ps6 := by
  unfold selected
  rw [pairs6]
  dsimp only
  rw [ms_eq6, aa_eq6]
  have h_ms6_keep0 := ms6_keep0
  have h_ms6_keep1 := ms6_keep1
  have h_ms6_keep2 := ms6_keep2
  have h_ms6_keep3 := ms6_keep3
  have h_ms6_keep4 := ms6_keep4
  have h_ms6_keep5 := ms6_keep5
  have h_ms6_keep6 := ms6_keep6
  have h_ms6_keep7 := ms6_keep7
  have h_ms6_keep8 := ms6_keep8
  have h_ms6_keep9 := ms6_keep9
  have h_ms6_keep10 := ms6_keep10
  have h_ms6_keep11 := ms6_keep11
  have h_ms6_keep12 := ms6_keep12
  have h_ms6_keep13 := ms6_keep13
  have h_ms6_keep14 := ms6_keep14
  have h_ms6_keep15 := ms6_keep15
  have h_ms6_keep16 := ms6_keep16
  have h_ms6_keep17 := ms6_keep17
  have h_ms6_keep18 := ms6_keep18
  have h_ms6_keep19 := ms6_keep19
  have h_ms6_keep20 := ms6_keep20
  have h_ms6_keep21 := ms6_keep21
  have h_ms6_keep22 := ms6_keep22
  have h_ms6_keep23 := ms6_keep23
  have h_ms6_keep24 := ms6_keep24
  have h_ms6_keep25 := ms6_keep25
  have h_ms6_keep26 := ms6_keep26
  have h_ms6_keep27 := ms6_keep27
  have h_ms6_keep28 := ms6_keep28
  have h_ms6_keep29 := ms6_keep29
  have h_ms6_keep30 := ms6_keep30
  have h_ms6_keep31 := ms6_keep31
  have h_ms6_keep32 := ms6_keep32
  have h_ms6_keep33 := ms6_keep33
  have h_ms6_keep34 := ms6_keep34
  have h_ms6_keep35 := ms6_keep35
  have h_ms6_keep36 := ms6_keep36
  have h_ms6_keep37 := ms6_keep37
  have h_ms6_keep38 := ms6_keep38
  have h_ms6_keep39 := ms6_keep39
  have h_ms6_keep40 := ms6_keep40
  have h_ms6_keep41 := ms6_keep41
  have h_ms6_keep42 := ms6_keep42
  have h_ms6_keep43 := ms6_keep43
  have h_ms6_keep44 := ms6_keep44
  have h_ms6_keep45 := ms6_keep45
  have h_ms6_keep46 := ms6_keep46
  have h_ms6_keep47 := ms6_keep47
  have h_ms6_keep48 := ms6_keep48
  have h_ms6_keep49 := ms6_keep49
  have h_ms6_keep50 := ms6_keep50
  have h_ms6_keep51 := ms6_keep51
  have h_ms6_keep52 := ms6_keep52
  have h_ms6_keep53 := ms6_keep53
  have h_ms6_keep54 := ms6_keep54
  have h_ms6_keep55 := ms6_keep55
  have h_ms6_keep56 := ms6_keep56
  have h_ms6_keep57 := ms6_keep57
  have h_ms6_keep58 := ms6_keep58
  have h_ms6_keep59 := ms6_keep59
  have h_ms6_keep60 := ms6_keep60
  have h_ms6_keep61 := ms6_keep61
  have h_ms6_keep62 := ms6_keep62
  have h_aa6_keep0 := aa6_keep0
  have h_aa6_keep1 := aa6_keep1
  have h_aa6_keep2 := aa6_keep2
  have h_aa6_keep3 := aa6_keep3
  have h_aa6_keep4 := aa6_keep4
  have h_aa6_keep5 := aa6_keep5
  have h_aa6_keep6 := aa6_keep6
  have h_aa6_keep7 := aa6_keep7
  have h_aa6_keep8 := aa6_keep8
  have h_aa6_keep9 := aa6_keep9
  have h_aa6_keep10 := aa6_keep10
  have h_aa6_keep11 := aa6_keep11
  have h_aa6_keep12 := aa6_keep12
  have h_aa6_keep13 := aa6_keep13
  have h_aa6_keep14 := aa6_keep14
  have h_aa6_keep15 := aa6_keep15
  have h_aa6_keep16 := aa6_keep16
  have h_aa6_keep17 := aa6_keep17
  have h_aa6_keep18 := aa6_keep18
  have h_aa6_keep19 := aa6_keep19
  have h_aa6_keep20 := aa6_keep20
  have h_aa6_keep21 := aa6_keep21
  have h_aa6_keep22 := aa6_keep22
  have h_aa6_keep23 := aa6_keep23
  have h_aa6_keep24 := aa6_keep24
  have h_aa6_keep25 := aa6_keep25
  have h_aa6_keep26 := aa6_keep26
  have h_aa6_keep27 := aa6_keep27
  have h_aa6_keep28 := aa6_keep28
  have h_aa6_keep29 := aa6_keep29
  have h_aa6_keep30 := aa6_keep30
  have h_aa6_keep31 := aa6_keep31
  have h_aa6_keep32 := aa6_keep32
  have h_aa6_keep33 := aa6_keep33
  have h_aa6_keep34 := aa6_keep34
  have h_aa6_keep35 := aa6_keep35
  have h_aa6_keep36 := aa6_keep36
  have h_aa6_keep37 := aa6_keep37
  have h_aa6_keep38 := aa6_keep38
  have h_aa6_keep39 := aa6_keep39
  have h_aa6_keep40 := aa6_keep40
  have h_aa6_keep41 := aa6_keep41
  have h_aa6_keep42 := aa6_keep42
  have h_aa6_keep43 := aa6_keep43
  have h_aa6_keep44 := aa6_keep44
  have h_aa6_keep45 := aa6_keep45
  have h_aa6_keep46 := aa6_keep46
  have h_aa6_keep47 := aa6_keep47
  have h_aa6_keep48 := aa6_keep48
  have h_aa6_keep49 := aa6_keep49
  have h_aa6_keep50 := aa6_keep50
  have h_aa6_keep51 := aa6_keep51
  simp only [div_one] at h_ms6_keep0 h_ms6_keep1 h_ms6_keep2 h_ms6_keep3 h_ms6_keep4 h_ms6_keep5 h_ms6_keep6 h_ms6_keep7 h_ms6_keep8 h_ms6_keep9 h_ms6_keep10 h_ms6_keep11 h_ms6_keep12 h_ms6_keep13 h_ms6_keep14 h_ms6_keep15 h_ms6_keep16 h_ms6_keep17 h_ms6_keep18 h_ms6_keep19 h_ms6_keep20 h_ms6_keep21 h_ms6_keep22 h_ms6_keep23 h_ms6_keep24 h_ms6_keep25 h_ms6_keep26 h_ms6_keep27 h_ms6_keep28 h_ms6_keep29 h_ms6_keep30 h_ms6_keep31 h_ms6_keep32 h_ms6_keep33 h_ms6_keep34 h_ms6_keep35 h_ms6_keep36 h_ms6_keep37 h_ms6_keep38 h_ms6_keep39 h_ms6_keep40 h_ms6_keep41 h_ms6_keep42 h_ms6_keep43 h_ms6_keep44 h_ms6_keep45 h_ms6_keep46 h_ms6_keep47 h_ms6_keep48 h_ms6_keep49 h_ms6_keep50 h_ms6_keep51 h_ms6_keep52 h_ms6_keep53 h_ms6_keep54 h_ms6_keep55 h_ms6_keep56 h_ms6_keep57 h_ms6_keep58 h_ms6_keep59 h_ms6_keep60 h_ms6_keep61 h_ms6_keep62 h_aa6_keep0 h_aa6_keep1 h_aa6_keep2 h_aa6_keep3 h_aa6_keep4 h_aa6_keep5 h_aa6_keep6 h_aa6_keep7 h_aa6_keep8 h_aa6_keep9 h_aa6_keep10 h_aa6_keep11 h_aa6_keep12 h_aa6_keep13 h_aa6_keep14 h_aa6_keep15 h_aa6_keep16 h_aa6_keep17 h_aa6_keep18 h_aa6_keep19 h_aa6_keep20 h_aa6_keep21 h_aa6_keep22 h_aa6_keep23 h_aa6_keep24 h_aa6_keep25 h_aa6_keep26 h_aa6_keep27 h_aa6_keep28 h_aa6_keep29 h_aa6_keep30 h_aa6_keep31 h_aa6_keep32 h_aa6_keep33 h_aa6_keep34 h_aa6_keep35 h_aa6_keep36 h_aa6_keep37 h_aa6_keep38 h_aa6_keep39 h_aa6_keep40 h_aa6_keep41 h_aa6_keep42 h_aa6_keep43 h_aa6_keep44 h_aa6_keep45 h_aa6_keep46 h_aa6_keep47 h_aa6_keep48 h_aa6_keep49 h_aa6_keep50 h_aa6_keep51
  norm_num [allps6, ps6, List.filter_cons, List.filter_nil, h_ms6_keep0, h_ms6_keep1, h_ms6_keep2, h_ms6_keep3, h_ms6_keep4, h_ms6_keep5, h_ms6_keep6, h_ms6_keep7, h_ms6_keep8, h_ms6_keep9, h_ms6_keep10, h_ms6_keep11, h_ms6_keep12, h_ms6_keep13, h_ms6_keep14, h_ms6_keep15, h_ms6_keep16, h_ms6_keep17, h_ms6_keep18, h_ms6_keep19, h_ms6_keep20, h_ms6_keep21, h_ms6_keep22, h_ms6_keep23, h_ms6_keep24, h_ms6_keep25, h_ms6_keep26, h_ms6_keep27, h_ms6_keep28, h_ms6_keep29, h_ms6_keep30, h_ms6_keep31, h_ms6_keep32, h_ms6_keep33, h_ms6_keep34, h_ms6_keep35, h_ms6_keep36, h_ms6_keep37, h_ms6_keep38, h_ms6_keep39, h_ms6_keep40, h_ms6_keep41, h_ms6_keep42, h_ms6_keep43, h_ms6_keep44, h_ms6_keep45, h_ms6_keep46, h_ms6_keep47, h_ms6_keep48, h_ms6_keep49, h_ms6_keep50, h_ms6_keep51, h_ms6_keep52, h_ms6_keep53, h_ms6_keep54, h_ms6_keep55, h_ms6_keep56, h_ms6_keep57, h_ms6_keep58, h_ms6_keep59, h_ms6_keep60, h_ms6_keep61, h_ms6_keep62, h_aa6_keep0, h_aa6_keep1, h_aa6_keep2, h_aa6_keep3, h_aa6_keep4, h_aa6_keep5, h_aa6_keep6, h_aa6_keep7, h_aa6_keep8, h_aa6_keep9, h_aa6_keep10, h_aa6_keep11, h_aa6_keep12, h_aa6_keep13, h_aa6_keep14, h_aa6_keep15, h_aa6_keep16, h_aa6_keep17, h_aa6_keep18, h_aa6_keep19, h_aa6_keep20, h_aa6_keep21, h_aa6_keep22, h_aa6_keep23, h_aa6_keep24, h_aa6_keep25, h_aa6_keep26, h_aa6_keep27, h_aa6_keep28, h_aa6_keep29, h_aa6_keep30, h_aa6_keep31, h_aa6_keep32, h_aa6_keep33, h_aa6_keep34, h_aa6_keep35, h_aa6_keep36, h_aa6_keep37, h_aa6_keep38, h_aa6_keep39, h_aa6_keep40, h_aa6_keep41, h_aa6_keep42, h_aa6_keep43, h_aa6_keep44, h_aa6_keep45, h_aa6_keep46, h_aa6_keep47, h_aa6_keep48, h_aa6_keep49, h_aa6_keep50, h_aa6_keep51]
end Proofs.Witness
