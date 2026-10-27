import Proofs.Ranks2
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace Proofs.Witness
theorem selected2 : selected matrix 2 3 = ps2 := by
  unfold selected
  rw [pairs2]
  dsimp only
  rw [ms_eq2, aa_eq2]
  have h_ms2_keep0 := ms2_keep0
  have h_ms2_keep1 := ms2_keep1
  have h_ms2_keep2 := ms2_keep2
  have h_ms2_keep3 := ms2_keep3
  have h_ms2_keep4 := ms2_keep4
  have h_ms2_keep5 := ms2_keep5
  have h_ms2_keep6 := ms2_keep6
  have h_ms2_keep7 := ms2_keep7
  have h_ms2_keep8 := ms2_keep8
  have h_ms2_keep9 := ms2_keep9
  have h_ms2_keep10 := ms2_keep10
  have h_ms2_keep11 := ms2_keep11
  have h_ms2_keep12 := ms2_keep12
  have h_ms2_keep13 := ms2_keep13
  have h_ms2_keep14 := ms2_keep14
  have h_ms2_keep15 := ms2_keep15
  have h_ms2_keep16 := ms2_keep16
  have h_ms2_keep17 := ms2_keep17
  have h_ms2_keep18 := ms2_keep18
  have h_ms2_keep19 := ms2_keep19
  have h_ms2_keep20 := ms2_keep20
  have h_ms2_keep21 := ms2_keep21
  have h_ms2_keep22 := ms2_keep22
  have h_ms2_keep23 := ms2_keep23
  have h_ms2_keep24 := ms2_keep24
  have h_ms2_keep25 := ms2_keep25
  have h_ms2_keep26 := ms2_keep26
  have h_ms2_keep27 := ms2_keep27
  have h_ms2_keep28 := ms2_keep28
  have h_ms2_keep29 := ms2_keep29
  have h_ms2_keep30 := ms2_keep30
  have h_ms2_keep31 := ms2_keep31
  have h_ms2_keep32 := ms2_keep32
  have h_ms2_keep33 := ms2_keep33
  have h_ms2_keep34 := ms2_keep34
  have h_ms2_keep35 := ms2_keep35
  have h_ms2_keep36 := ms2_keep36
  have h_ms2_keep37 := ms2_keep37
  have h_ms2_keep38 := ms2_keep38
  have h_ms2_keep39 := ms2_keep39
  have h_ms2_keep40 := ms2_keep40
  have h_ms2_keep41 := ms2_keep41
  have h_ms2_keep42 := ms2_keep42
  have h_ms2_keep43 := ms2_keep43
  have h_ms2_keep44 := ms2_keep44
  have h_ms2_keep45 := ms2_keep45
  have h_ms2_keep46 := ms2_keep46
  have h_ms2_keep47 := ms2_keep47
  have h_ms2_keep48 := ms2_keep48
  have h_ms2_keep49 := ms2_keep49
  have h_ms2_keep50 := ms2_keep50
  have h_ms2_keep51 := ms2_keep51
  have h_ms2_keep52 := ms2_keep52
  have h_ms2_keep53 := ms2_keep53
  have h_ms2_keep54 := ms2_keep54
  have h_ms2_keep55 := ms2_keep55
  have h_ms2_keep56 := ms2_keep56
  have h_ms2_keep57 := ms2_keep57
  have h_ms2_keep58 := ms2_keep58
  have h_ms2_keep59 := ms2_keep59
  have h_aa2_keep0 := aa2_keep0
  have h_aa2_keep1 := aa2_keep1
  have h_aa2_keep2 := aa2_keep2
  have h_aa2_keep3 := aa2_keep3
  have h_aa2_keep4 := aa2_keep4
  have h_aa2_keep5 := aa2_keep5
  have h_aa2_keep6 := aa2_keep6
  have h_aa2_keep7 := aa2_keep7
  have h_aa2_keep8 := aa2_keep8
  have h_aa2_keep9 := aa2_keep9
  have h_aa2_keep10 := aa2_keep10
  have h_aa2_keep11 := aa2_keep11
  have h_aa2_keep12 := aa2_keep12
  have h_aa2_keep13 := aa2_keep13
  have h_aa2_keep14 := aa2_keep14
  have h_aa2_keep15 := aa2_keep15
  have h_aa2_keep16 := aa2_keep16
  have h_aa2_keep17 := aa2_keep17
  have h_aa2_keep18 := aa2_keep18
  have h_aa2_keep19 := aa2_keep19
  have h_aa2_keep20 := aa2_keep20
  have h_aa2_keep21 := aa2_keep21
  have h_aa2_keep22 := aa2_keep22
  have h_aa2_keep23 := aa2_keep23
  have h_aa2_keep24 := aa2_keep24
  have h_aa2_keep25 := aa2_keep25
  have h_aa2_keep26 := aa2_keep26
  have h_aa2_keep27 := aa2_keep27
  have h_aa2_keep28 := aa2_keep28
  have h_aa2_keep29 := aa2_keep29
  have h_aa2_keep30 := aa2_keep30
  have h_aa2_keep31 := aa2_keep31
  have h_aa2_keep32 := aa2_keep32
  have h_aa2_keep33 := aa2_keep33
  have h_aa2_keep34 := aa2_keep34
  have h_aa2_keep35 := aa2_keep35
  have h_aa2_keep36 := aa2_keep36
  have h_aa2_keep37 := aa2_keep37
  have h_aa2_keep38 := aa2_keep38
  have h_aa2_keep39 := aa2_keep39
  have h_aa2_keep40 := aa2_keep40
  have h_aa2_keep41 := aa2_keep41
  have h_aa2_keep42 := aa2_keep42
  have h_aa2_keep43 := aa2_keep43
  have h_aa2_keep44 := aa2_keep44
  have h_aa2_keep45 := aa2_keep45
  have h_aa2_keep46 := aa2_keep46
  have h_aa2_keep47 := aa2_keep47
  simp only [div_one] at h_ms2_keep0 h_ms2_keep1 h_ms2_keep2 h_ms2_keep3 h_ms2_keep4 h_ms2_keep5 h_ms2_keep6 h_ms2_keep7 h_ms2_keep8 h_ms2_keep9 h_ms2_keep10 h_ms2_keep11 h_ms2_keep12 h_ms2_keep13 h_ms2_keep14 h_ms2_keep15 h_ms2_keep16 h_ms2_keep17 h_ms2_keep18 h_ms2_keep19 h_ms2_keep20 h_ms2_keep21 h_ms2_keep22 h_ms2_keep23 h_ms2_keep24 h_ms2_keep25 h_ms2_keep26 h_ms2_keep27 h_ms2_keep28 h_ms2_keep29 h_ms2_keep30 h_ms2_keep31 h_ms2_keep32 h_ms2_keep33 h_ms2_keep34 h_ms2_keep35 h_ms2_keep36 h_ms2_keep37 h_ms2_keep38 h_ms2_keep39 h_ms2_keep40 h_ms2_keep41 h_ms2_keep42 h_ms2_keep43 h_ms2_keep44 h_ms2_keep45 h_ms2_keep46 h_ms2_keep47 h_ms2_keep48 h_ms2_keep49 h_ms2_keep50 h_ms2_keep51 h_ms2_keep52 h_ms2_keep53 h_ms2_keep54 h_ms2_keep55 h_ms2_keep56 h_ms2_keep57 h_ms2_keep58 h_ms2_keep59 h_aa2_keep0 h_aa2_keep1 h_aa2_keep2 h_aa2_keep3 h_aa2_keep4 h_aa2_keep5 h_aa2_keep6 h_aa2_keep7 h_aa2_keep8 h_aa2_keep9 h_aa2_keep10 h_aa2_keep11 h_aa2_keep12 h_aa2_keep13 h_aa2_keep14 h_aa2_keep15 h_aa2_keep16 h_aa2_keep17 h_aa2_keep18 h_aa2_keep19 h_aa2_keep20 h_aa2_keep21 h_aa2_keep22 h_aa2_keep23 h_aa2_keep24 h_aa2_keep25 h_aa2_keep26 h_aa2_keep27 h_aa2_keep28 h_aa2_keep29 h_aa2_keep30 h_aa2_keep31 h_aa2_keep32 h_aa2_keep33 h_aa2_keep34 h_aa2_keep35 h_aa2_keep36 h_aa2_keep37 h_aa2_keep38 h_aa2_keep39 h_aa2_keep40 h_aa2_keep41 h_aa2_keep42 h_aa2_keep43 h_aa2_keep44 h_aa2_keep45 h_aa2_keep46 h_aa2_keep47
  norm_num [allps2, ps2, List.filter_cons, List.filter_nil, h_ms2_keep0, h_ms2_keep1, h_ms2_keep2, h_ms2_keep3, h_ms2_keep4, h_ms2_keep5, h_ms2_keep6, h_ms2_keep7, h_ms2_keep8, h_ms2_keep9, h_ms2_keep10, h_ms2_keep11, h_ms2_keep12, h_ms2_keep13, h_ms2_keep14, h_ms2_keep15, h_ms2_keep16, h_ms2_keep17, h_ms2_keep18, h_ms2_keep19, h_ms2_keep20, h_ms2_keep21, h_ms2_keep22, h_ms2_keep23, h_ms2_keep24, h_ms2_keep25, h_ms2_keep26, h_ms2_keep27, h_ms2_keep28, h_ms2_keep29, h_ms2_keep30, h_ms2_keep31, h_ms2_keep32, h_ms2_keep33, h_ms2_keep34, h_ms2_keep35, h_ms2_keep36, h_ms2_keep37, h_ms2_keep38, h_ms2_keep39, h_ms2_keep40, h_ms2_keep41, h_ms2_keep42, h_ms2_keep43, h_ms2_keep44, h_ms2_keep45, h_ms2_keep46, h_ms2_keep47, h_ms2_keep48, h_ms2_keep49, h_ms2_keep50, h_ms2_keep51, h_ms2_keep52, h_ms2_keep53, h_ms2_keep54, h_ms2_keep55, h_ms2_keep56, h_ms2_keep57, h_ms2_keep58, h_ms2_keep59, h_aa2_keep0, h_aa2_keep1, h_aa2_keep2, h_aa2_keep3, h_aa2_keep4, h_aa2_keep5, h_aa2_keep6, h_aa2_keep7, h_aa2_keep8, h_aa2_keep9, h_aa2_keep10, h_aa2_keep11, h_aa2_keep12, h_aa2_keep13, h_aa2_keep14, h_aa2_keep15, h_aa2_keep16, h_aa2_keep17, h_aa2_keep18, h_aa2_keep19, h_aa2_keep20, h_aa2_keep21, h_aa2_keep22, h_aa2_keep23, h_aa2_keep24, h_aa2_keep25, h_aa2_keep26, h_aa2_keep27, h_aa2_keep28, h_aa2_keep29, h_aa2_keep30, h_aa2_keep31, h_aa2_keep32, h_aa2_keep33, h_aa2_keep34, h_aa2_keep35, h_aa2_keep36, h_aa2_keep37, h_aa2_keep38, h_aa2_keep39, h_aa2_keep40, h_aa2_keep41, h_aa2_keep42, h_aa2_keep43, h_aa2_keep44, h_aa2_keep45, h_aa2_keep46, h_aa2_keep47]
end Proofs.Witness
