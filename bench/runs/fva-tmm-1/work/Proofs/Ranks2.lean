import Proofs.WitnessData
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Proofs.Witness
def ps2 : List (Nat × Nat) := [(4, 4), (2, 2), (2, 2), (3, 4), (1, 1), (2, 3), (4, 4), (3, 4), (5, 9), (1, 1), (2, 3), (2, 3), (3, 3), (1, 1), (4, 6), (4, 5), (4, 7), (1, 1), (2, 2), (2, 2), (1, 1), (1, 1), (1, 1), (1, 1), (2, 3), (2, 3), (3, 3), (2, 2), (1, 1), (1, 1), (3, 4), (3, 3), (1, 1), (4, 4), (2, 2), (2, 2), (5, 6), (2, 2), (1, 1), (1, 1), (2, 2), (1, 1), (1, 1), (1, 1), (3, 3), (2, 2), (1, 1), (7, 8), (4, 6), (2, 3), (4, 5), (3, 5), (1, 1), (1, 1), (2, 2), (1, 1), (1, 1), (2, 2), (1, 1), (1, 1), (4, 5), (2, 3), (2, 2), (3, 3), (6, 9), (4, 5), (1, 1), (5, 8), (1, 1), (2, 3), (1, 1), (1, 1), (1, 1), (5, 7), (6, 6), (2, 2)]
def allps2 : List (Nat × Nat) := [(4, 4), (2, 2), (2, 1), (5, 4), (14, 10), (5, 3), (2, 2), (1, 8), (3, 4), (1, 1), (2, 3), (4, 16), (1, 2), (4, 4), (3, 4), (5, 9), (4, 11), (1, 1), (2, 3), (2, 1), (2, 3), (3, 3), (1, 1), (4, 6), (1, 2), (3, 2), (5, 1), (3, 1), (2, 1), (4, 5), (2, 1), (4, 7), (1, 1), (9, 7), (2, 2), (2, 5), (1, 3), (2, 2), (3, 1), (4, 9), (1, 1), (6, 25), (1, 1), (1, 3), (4, 11), (3, 9), (1, 3), (1, 1), (1, 1), (5, 12), (1, 2), (1, 12), (2, 1), (4, 17), (2, 3), (7, 4), (1, 2), (1, 2), (1, 3), (6, 3), (4, 2), (2, 3), (6, 1), (1, 19), (3, 3), (9, 5), (2, 2), (2, 1), (3, 1), (5, 16), (1, 1), (1, 1), (3, 4), (3, 3), (11, 16), (4, 3), (1, 2), (9, 13), (3, 1), (1, 2), (1, 1), (4, 4), (1, 4), (2, 2), (2, 2), (1, 9), (2, 29), (9, 9), (4, 8), (4, 9), (5, 6), (2, 2), (1, 1), (2, 5), (1, 1), (4, 1), (2, 2), (1, 1), (1, 2), (1, 3), (2, 1), (5, 2), (2, 1), (1, 3), (6, 1), (3, 1), (1, 1), (1, 1), (5, 1), (3, 3), (2, 2), (1, 1), (2, 1), (7, 8), (2, 7), (4, 6), (1, 2), (3, 2), (2, 1), (2, 3), (4, 5), (2, 1), (3, 8), (3, 5), (2, 1), (3, 2), (5, 13), (9, 2), (4, 1), (1, 1), (10, 6), (10, 11), (1, 2), (5, 2), (1, 1), (2, 5), (2, 2), (2, 10), (1, 1), (2, 1), (3, 23), (1, 1), (1, 5), (7, 2), (2, 2), (1, 2), (15, 4), (1, 1), (1, 1), (4, 5), (1, 3), (2, 4), (1, 10), (2, 3), (2, 2), (3, 3), (6, 9), (4, 5), (3, 7), (1, 1), (3, 2), (5, 8), (1, 5), (1, 3), (1, 9), (1, 2), (2, 4), (1, 3), (3, 6), (11, 4), (3, 11), (6, 2), (1, 1), (2, 3), (1, 3), (3, 1), (2, 9), (1, 2), (1, 3), (4, 2), (2, 6), (1, 1), (2, 5), (7, 11), (8, 10), (14, 9), (2, 1), (6, 3), (1, 2), (14, 5), (3, 1), (1, 1), (1, 6), (1, 1), (5, 7), (6, 6), (1, 2), (1, 2), (9, 3), (3, 1), (5, 1), (5, 10), (1, 9), (2, 2), (5, 1)]
def ms2 : List ℚ := [(1 / 1), (1 / 1), (2 / 1), (5 / 4), (7 / 5), (5 / 3), (1 / 1), (1 / 8), (3 / 4), (1 / 1), (2 / 3), (1 / 4), (1 / 2), (1 / 1), (3 / 4), (5 / 9), (4 / 11), (1 / 1), (2 / 3), (2 / 1), (2 / 3), (1 / 1), (1 / 1), (2 / 3), (1 / 2), (3 / 2), (5 / 1), (3 / 1), (2 / 1), (4 / 5), (2 / 1), (4 / 7), (1 / 1), (9 / 7), (1 / 1), (2 / 5), (1 / 3), (1 / 1), (3 / 1), (4 / 9), (1 / 1), (6 / 25), (1 / 1), (1 / 3), (4 / 11), (1 / 3), (1 / 3), (1 / 1), (1 / 1), (5 / 12), (1 / 2), (1 / 12), (2 / 1), (4 / 17), (2 / 3), (7 / 4), (1 / 2), (1 / 2), (1 / 3), (2 / 1), (2 / 1), (2 / 3), (6 / 1), (1 / 19), (1 / 1), (9 / 5), (1 / 1), (2 / 1), (3 / 1), (5 / 16), (1 / 1), (1 / 1), (3 / 4), (1 / 1), (11 / 16), (4 / 3), (1 / 2), (9 / 13), (3 / 1), (1 / 2), (1 / 1), (1 / 1), (1 / 4), (1 / 1), (1 / 1), (1 / 9), (2 / 29), (1 / 1), (1 / 2), (4 / 9), (5 / 6), (1 / 1), (1 / 1), (2 / 5), (1 / 1), (4 / 1), (1 / 1), (1 / 1), (1 / 2), (1 / 3), (2 / 1), (5 / 2), (2 / 1), (1 / 3), (6 / 1), (3 / 1), (1 / 1), (1 / 1), (5 / 1), (1 / 1), (1 / 1), (1 / 1), (2 / 1), (7 / 8), (2 / 7), (2 / 3), (1 / 2), (3 / 2), (2 / 1), (2 / 3), (4 / 5), (2 / 1), (3 / 8), (3 / 5), (2 / 1), (3 / 2), (5 / 13), (9 / 2), (4 / 1), (1 / 1), (5 / 3), (10 / 11), (1 / 2), (5 / 2), (1 / 1), (2 / 5), (1 / 1), (1 / 5), (1 / 1), (2 / 1), (3 / 23), (1 / 1), (1 / 5), (7 / 2), (1 / 1), (1 / 2), (15 / 4), (1 / 1), (1 / 1), (4 / 5), (1 / 3), (1 / 2), (1 / 10), (2 / 3), (1 / 1), (1 / 1), (2 / 3), (4 / 5), (3 / 7), (1 / 1), (3 / 2), (5 / 8), (1 / 5), (1 / 3), (1 / 9), (1 / 2), (1 / 2), (1 / 3), (1 / 2), (11 / 4), (3 / 11), (3 / 1), (1 / 1), (2 / 3), (1 / 3), (3 / 1), (2 / 9), (1 / 2), (1 / 3), (2 / 1), (1 / 3), (1 / 1), (2 / 5), (7 / 11), (4 / 5), (14 / 9), (2 / 1), (2 / 1), (1 / 2), (14 / 5), (3 / 1), (1 / 1), (1 / 6), (1 / 1), (5 / 7), (1 / 1), (1 / 2), (1 / 2), (3 / 1), (3 / 1), (5 / 1), (1 / 2), (1 / 9), (1 / 1), (5 / 1)]
def aa2 : List ℚ := [16, 4, 2, 20, 140, 15, 4, 8, 12, 1, 6, 64, 2, 16, 12, 45, 44, 1, 6, 2, 6, 9, 1, 24, 2, 6, 5, 3, 2, 20, 2, 28, 1, 63, 4, 10, 3, 4, 3, 36, 1, 150, 1, 3, 44, 27, 3, 1, 1, 60, 2, 12, 2, 68, 6, 28, 2, 2, 3, 18, 8, 6, 6, 19, 9, 45, 4, 2, 3, 80, 1, 1, 12, 9, 176, 12, 2, 117, 3, 2, 1, 16, 4, 4, 4, 9, 58, 81, 32, 36, 30, 4, 1, 10, 1, 4, 4, 1, 2, 3, 2, 10, 2, 3, 6, 3, 1, 1, 5, 9, 4, 1, 2, 56, 14, 24, 2, 6, 2, 6, 20, 2, 24, 15, 2, 6, 65, 18, 4, 1, 60, 110, 2, 10, 1, 10, 4, 20, 1, 2, 69, 1, 5, 14, 4, 2, 60, 1, 1, 20, 3, 8, 10, 6, 4, 9, 54, 20, 21, 1, 6, 40, 5, 3, 9, 2, 8, 3, 18, 44, 33, 12, 1, 6, 3, 3, 18, 2, 3, 8, 12, 1, 10, 77, 80, 126, 2, 18, 2, 70, 3, 1, 6, 1, 35, 36, 2, 2, 27, 3, 5, 50, 9, 4, 5]
theorem pairs2 : pairs matrix 2 3 = allps2 := by kernel_rfl
theorem ms_eq2 : allps2.map (fun p => (p.1 : ℚ) / p.2) = ms2 := by kernel_rfl
theorem aa_eq2 : allps2.map (fun p => ((p.1 * p.2 : Nat) : ℚ)) = aa2 := by kernel_rfl
theorem ms2_length : ms2.length = 205 := by kernel_rfl
theorem ms2_rank0 : rank2 ms2 (1 / 19) = 2 := by kernel_rfl
theorem ms2_keep0 : rankKeep ms2 (1 / 19) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank0]
  decide +kernel
theorem ms2_rank1 : rank2 ms2 (2 / 29) = 4 := by kernel_rfl
theorem ms2_keep1 : rankKeep ms2 (2 / 29) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank1]
  decide +kernel
theorem ms2_rank2 : rank2 ms2 (1 / 12) = 6 := by kernel_rfl
theorem ms2_keep2 : rankKeep ms2 (1 / 12) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank2]
  decide +kernel
theorem ms2_rank3 : rank2 ms2 (1 / 10) = 8 := by kernel_rfl
theorem ms2_keep3 : rankKeep ms2 (1 / 10) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank3]
  decide +kernel
theorem ms2_rank4 : rank2 ms2 (1 / 9) = 12 := by kernel_rfl
theorem ms2_keep4 : rankKeep ms2 (1 / 9) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank4]
  decide +kernel
theorem ms2_rank5 : rank2 ms2 (1 / 8) = 16 := by kernel_rfl
theorem ms2_keep5 : rankKeep ms2 (1 / 8) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank5]
  decide +kernel
theorem ms2_rank6 : rank2 ms2 (3 / 23) = 18 := by kernel_rfl
theorem ms2_keep6 : rankKeep ms2 (3 / 23) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank6]
  decide +kernel
theorem ms2_rank7 : rank2 ms2 (1 / 6) = 20 := by kernel_rfl
theorem ms2_keep7 : rankKeep ms2 (1 / 6) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank7]
  decide +kernel
theorem ms2_rank8 : rank2 ms2 (1 / 5) = 24 := by kernel_rfl
theorem ms2_keep8 : rankKeep ms2 (1 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank8]
  decide +kernel
theorem ms2_rank9 : rank2 ms2 (2 / 9) = 28 := by kernel_rfl
theorem ms2_keep9 : rankKeep ms2 (2 / 9) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank9]
  decide +kernel
theorem ms2_rank10 : rank2 ms2 (4 / 17) = 30 := by kernel_rfl
theorem ms2_keep10 : rankKeep ms2 (4 / 17) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank10]
  decide +kernel
theorem ms2_rank11 : rank2 ms2 (6 / 25) = 32 := by kernel_rfl
theorem ms2_keep11 : rankKeep ms2 (6 / 25) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank11]
  decide +kernel
theorem ms2_rank12 : rank2 ms2 (1 / 4) = 35 := by kernel_rfl
theorem ms2_keep12 : rankKeep ms2 (1 / 4) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank12]
  decide +kernel
theorem ms2_rank13 : rank2 ms2 (3 / 11) = 38 := by kernel_rfl
theorem ms2_keep13 : rankKeep ms2 (3 / 11) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank13]
  decide +kernel
theorem ms2_rank14 : rank2 ms2 (2 / 7) = 40 := by kernel_rfl
theorem ms2_keep14 : rankKeep ms2 (2 / 7) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank14]
  decide +kernel
theorem ms2_rank15 : rank2 ms2 (5 / 16) = 42 := by kernel_rfl
theorem ms2_keep15 : rankKeep ms2 (5 / 16) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank15]
  decide +kernel
theorem ms2_rank16 : rank2 ms2 (1 / 3) = 56 := by kernel_rfl
theorem ms2_keep16 : rankKeep ms2 (1 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank16]
  decide +kernel
theorem ms2_rank17 : rank2 ms2 (4 / 11) = 71 := by kernel_rfl
theorem ms2_keep17 : rankKeep ms2 (4 / 11) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank17]
  decide +kernel
theorem ms2_rank18 : rank2 ms2 (3 / 8) = 74 := by kernel_rfl
theorem ms2_keep18 : rankKeep ms2 (3 / 8) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank18]
  decide +kernel
theorem ms2_rank19 : rank2 ms2 (5 / 13) = 76 := by kernel_rfl
theorem ms2_keep19 : rankKeep ms2 (5 / 13) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank19]
  decide +kernel
theorem ms2_rank20 : rank2 ms2 (2 / 5) = 81 := by kernel_rfl
theorem ms2_keep20 : rankKeep ms2 (2 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank20]
  decide +kernel
theorem ms2_rank21 : rank2 ms2 (5 / 12) = 86 := by kernel_rfl
theorem ms2_keep21 : rankKeep ms2 (5 / 12) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank21]
  decide +kernel
theorem ms2_rank22 : rank2 ms2 (3 / 7) = 88 := by kernel_rfl
theorem ms2_keep22 : rankKeep ms2 (3 / 7) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank22]
  decide +kernel
theorem ms2_rank23 : rank2 ms2 (4 / 9) = 91 := by kernel_rfl
theorem ms2_keep23 : rankKeep ms2 (4 / 9) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank23]
  decide +kernel
theorem ms2_rank24 : rank2 ms2 (1 / 2) = 114 := by kernel_rfl
theorem ms2_keep24 : rankKeep ms2 (1 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank24]
  decide +kernel
theorem ms2_rank25 : rank2 ms2 (5 / 9) = 136 := by kernel_rfl
theorem ms2_keep25 : rankKeep ms2 (5 / 9) 3 10 = true := by
  unfold rankKeep
  rw [ms2_length, ms2_rank25]
  decide +kernel
theorem ms2_rank26 : rank2 ms2 (4 / 7) = 138 := by kernel_rfl
theorem ms2_keep26 : rankKeep ms2 (4 / 7) 3 10 = true := by
  unfold rankKeep
  rw [ms2_length, ms2_rank26]
  decide +kernel
theorem ms2_rank27 : rank2 ms2 (3 / 5) = 140 := by kernel_rfl
theorem ms2_keep27 : rankKeep ms2 (3 / 5) 3 10 = true := by
  unfold rankKeep
  rw [ms2_length, ms2_rank27]
  decide +kernel
theorem ms2_rank28 : rank2 ms2 (5 / 8) = 142 := by kernel_rfl
theorem ms2_keep28 : rankKeep ms2 (5 / 8) 3 10 = true := by
  unfold rankKeep
  rw [ms2_length, ms2_rank28]
  decide +kernel
theorem ms2_rank29 : rank2 ms2 (7 / 11) = 144 := by kernel_rfl
theorem ms2_keep29 : rankKeep ms2 (7 / 11) 3 10 = true := by
  unfold rankKeep
  rw [ms2_length, ms2_rank29]
  decide +kernel
theorem ms2_rank30 : rank2 ms2 (2 / 3) = 156 := by kernel_rfl
theorem ms2_keep30 : rankKeep ms2 (2 / 3) 3 10 = true := by
  unfold rankKeep
  rw [ms2_length, ms2_rank30]
  decide +kernel
theorem ms2_rank31 : rank2 ms2 (11 / 16) = 168 := by kernel_rfl
theorem ms2_keep31 : rankKeep ms2 (11 / 16) 3 10 = true := by
  unfold rankKeep
  rw [ms2_length, ms2_rank31]
  decide +kernel
theorem ms2_rank32 : rank2 ms2 (9 / 13) = 170 := by kernel_rfl
theorem ms2_keep32 : rankKeep ms2 (9 / 13) 3 10 = true := by
  unfold rankKeep
  rw [ms2_length, ms2_rank32]
  decide +kernel
theorem ms2_rank33 : rank2 ms2 (5 / 7) = 172 := by kernel_rfl
theorem ms2_keep33 : rankKeep ms2 (5 / 7) 3 10 = true := by
  unfold rankKeep
  rw [ms2_length, ms2_rank33]
  decide +kernel
theorem ms2_rank34 : rank2 ms2 (3 / 4) = 176 := by kernel_rfl
theorem ms2_keep34 : rankKeep ms2 (3 / 4) 3 10 = true := by
  unfold rankKeep
  rw [ms2_length, ms2_rank34]
  decide +kernel
theorem ms2_rank35 : rank2 ms2 (4 / 5) = 184 := by kernel_rfl
theorem ms2_keep35 : rankKeep ms2 (4 / 5) 3 10 = true := by
  unfold rankKeep
  rw [ms2_length, ms2_rank35]
  decide +kernel
theorem ms2_rank36 : rank2 ms2 (5 / 6) = 190 := by kernel_rfl
theorem ms2_keep36 : rankKeep ms2 (5 / 6) 3 10 = true := by
  unfold rankKeep
  rw [ms2_length, ms2_rank36]
  decide +kernel
theorem ms2_rank37 : rank2 ms2 (7 / 8) = 192 := by kernel_rfl
theorem ms2_keep37 : rankKeep ms2 (7 / 8) 3 10 = true := by
  unfold rankKeep
  rw [ms2_length, ms2_rank37]
  decide +kernel
theorem ms2_rank38 : rank2 ms2 (10 / 11) = 194 := by kernel_rfl
theorem ms2_keep38 : rankKeep ms2 (10 / 11) 3 10 = true := by
  unfold rankKeep
  rw [ms2_length, ms2_rank38]
  decide +kernel
theorem ms2_rank39 : rank2 ms2 (1 / 1) = 247 := by kernel_rfl
theorem ms2_keep39 : rankKeep ms2 (1 / 1) 3 10 = true := by
  unfold rankKeep
  rw [ms2_length, ms2_rank39]
  decide +kernel
theorem ms2_rank40 : rank2 ms2 (5 / 4) = 300 := by kernel_rfl
theorem ms2_keep40 : rankKeep ms2 (5 / 4) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank40]
  decide +kernel
theorem ms2_rank41 : rank2 ms2 (9 / 7) = 302 := by kernel_rfl
theorem ms2_keep41 : rankKeep ms2 (9 / 7) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank41]
  decide +kernel
theorem ms2_rank42 : rank2 ms2 (4 / 3) = 304 := by kernel_rfl
theorem ms2_keep42 : rankKeep ms2 (4 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank42]
  decide +kernel
theorem ms2_rank43 : rank2 ms2 (7 / 5) = 306 := by kernel_rfl
theorem ms2_keep43 : rankKeep ms2 (7 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank43]
  decide +kernel
theorem ms2_rank44 : rank2 ms2 (3 / 2) = 311 := by kernel_rfl
theorem ms2_keep44 : rankKeep ms2 (3 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank44]
  decide +kernel
theorem ms2_rank45 : rank2 ms2 (14 / 9) = 316 := by kernel_rfl
theorem ms2_keep45 : rankKeep ms2 (14 / 9) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank45]
  decide +kernel
theorem ms2_rank46 : rank2 ms2 (5 / 3) = 319 := by kernel_rfl
theorem ms2_keep46 : rankKeep ms2 (5 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank46]
  decide +kernel
theorem ms2_rank47 : rank2 ms2 (7 / 4) = 322 := by kernel_rfl
theorem ms2_keep47 : rankKeep ms2 (7 / 4) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank47]
  decide +kernel
theorem ms2_rank48 : rank2 ms2 (9 / 5) = 324 := by kernel_rfl
theorem ms2_keep48 : rankKeep ms2 (9 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank48]
  decide +kernel
theorem ms2_rank49 : rank2 ms2 (2 / 1) = 343 := by kernel_rfl
theorem ms2_keep49 : rankKeep ms2 (2 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank49]
  decide +kernel
theorem ms2_rank50 : rank2 ms2 (5 / 2) = 363 := by kernel_rfl
theorem ms2_keep50 : rankKeep ms2 (5 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank50]
  decide +kernel
theorem ms2_rank51 : rank2 ms2 (11 / 4) = 366 := by kernel_rfl
theorem ms2_keep51 : rankKeep ms2 (11 / 4) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank51]
  decide +kernel
theorem ms2_rank52 : rank2 ms2 (14 / 5) = 368 := by kernel_rfl
theorem ms2_keep52 : rankKeep ms2 (14 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank52]
  decide +kernel
theorem ms2_rank53 : rank2 ms2 (3 / 1) = 379 := by kernel_rfl
theorem ms2_keep53 : rankKeep ms2 (3 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank53]
  decide +kernel
theorem ms2_rank54 : rank2 ms2 (7 / 2) = 390 := by kernel_rfl
theorem ms2_keep54 : rankKeep ms2 (7 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank54]
  decide +kernel
theorem ms2_rank55 : rank2 ms2 (15 / 4) = 392 := by kernel_rfl
theorem ms2_keep55 : rankKeep ms2 (15 / 4) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank55]
  decide +kernel
theorem ms2_rank56 : rank2 ms2 (4 / 1) = 395 := by kernel_rfl
theorem ms2_keep56 : rankKeep ms2 (4 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank56]
  decide +kernel
theorem ms2_rank57 : rank2 ms2 (9 / 2) = 398 := by kernel_rfl
theorem ms2_keep57 : rankKeep ms2 (9 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank57]
  decide +kernel
theorem ms2_rank58 : rank2 ms2 (5 / 1) = 403 := by kernel_rfl
theorem ms2_keep58 : rankKeep ms2 (5 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank58]
  decide +kernel
theorem ms2_rank59 : rank2 ms2 (6 / 1) = 409 := by kernel_rfl
theorem ms2_keep59 : rankKeep ms2 (6 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms2_length, ms2_rank59]
  decide +kernel
theorem aa2_length : aa2.length = 205 := by kernel_rfl
theorem aa2_rank0 : rank2 aa2 (1 / 1) = 29 := by kernel_rfl
theorem aa2_keep0 : rankKeep aa2 (1 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank0]
  decide +kernel
theorem aa2_rank1 : rank2 aa2 (2 / 1) = 87 := by kernel_rfl
theorem aa2_keep1 : rankKeep aa2 (2 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank1]
  decide +kernel
theorem aa2_rank2 : rank2 aa2 (3 / 1) = 136 := by kernel_rfl
theorem aa2_keep2 : rankKeep aa2 (3 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank2]
  decide +kernel
theorem aa2_rank3 : rank2 aa2 (4 / 1) = 172 := by kernel_rfl
theorem aa2_keep3 : rankKeep aa2 (4 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank3]
  decide +kernel
theorem aa2_rank4 : rank2 aa2 (5 / 1) = 195 := by kernel_rfl
theorem aa2_keep4 : rankKeep aa2 (5 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank4]
  decide +kernel
theorem aa2_rank5 : rank2 aa2 (6 / 1) = 216 := by kernel_rfl
theorem aa2_keep5 : rankKeep aa2 (6 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank5]
  decide +kernel
theorem aa2_rank6 : rank2 aa2 (8 / 1) = 236 := by kernel_rfl
theorem aa2_keep6 : rankKeep aa2 (8 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank6]
  decide +kernel
theorem aa2_rank7 : rank2 aa2 (9 / 1) = 249 := by kernel_rfl
theorem aa2_keep7 : rankKeep aa2 (9 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank7]
  decide +kernel
theorem aa2_rank8 : rank2 aa2 (10 / 1) = 264 := by kernel_rfl
theorem aa2_keep8 : rankKeep aa2 (10 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank8]
  decide +kernel
theorem aa2_rank9 : rank2 aa2 (12 / 1) = 278 := by kernel_rfl
theorem aa2_keep9 : rankKeep aa2 (12 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank9]
  decide +kernel
theorem aa2_rank10 : rank2 aa2 (14 / 1) = 287 := by kernel_rfl
theorem aa2_keep10 : rankKeep aa2 (14 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank10]
  decide +kernel
theorem aa2_rank11 : rank2 aa2 (15 / 1) = 291 := by kernel_rfl
theorem aa2_keep11 : rankKeep aa2 (15 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank11]
  decide +kernel
theorem aa2_rank12 : rank2 aa2 (16 / 1) = 296 := by kernel_rfl
theorem aa2_keep12 : rankKeep aa2 (16 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank12]
  decide +kernel
theorem aa2_rank13 : rank2 aa2 (18 / 1) = 304 := by kernel_rfl
theorem aa2_keep13 : rankKeep aa2 (18 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank13]
  decide +kernel
theorem aa2_rank14 : rank2 aa2 (19 / 1) = 310 := by kernel_rfl
theorem aa2_keep14 : rankKeep aa2 (19 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank14]
  decide +kernel
theorem aa2_rank15 : rank2 aa2 (20 / 1) = 317 := by kernel_rfl
theorem aa2_keep15 : rankKeep aa2 (20 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank15]
  decide +kernel
theorem aa2_rank16 : rank2 aa2 (21 / 1) = 324 := by kernel_rfl
theorem aa2_keep16 : rankKeep aa2 (21 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank16]
  decide +kernel
theorem aa2_rank17 : rank2 aa2 (24 / 1) = 328 := by kernel_rfl
theorem aa2_keep17 : rankKeep aa2 (24 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank17]
  decide +kernel
theorem aa2_rank18 : rank2 aa2 (27 / 1) = 333 := by kernel_rfl
theorem aa2_keep18 : rankKeep aa2 (27 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank18]
  decide +kernel
theorem aa2_rank19 : rank2 aa2 (28 / 1) = 337 := by kernel_rfl
theorem aa2_keep19 : rankKeep aa2 (28 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank19]
  decide +kernel
theorem aa2_rank20 : rank2 aa2 (30 / 1) = 340 := by kernel_rfl
theorem aa2_keep20 : rankKeep aa2 (30 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank20]
  decide +kernel
theorem aa2_rank21 : rank2 aa2 (32 / 1) = 342 := by kernel_rfl
theorem aa2_keep21 : rankKeep aa2 (32 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank21]
  decide +kernel
theorem aa2_rank22 : rank2 aa2 (33 / 1) = 344 := by kernel_rfl
theorem aa2_keep22 : rankKeep aa2 (33 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank22]
  decide +kernel
theorem aa2_rank23 : rank2 aa2 (35 / 1) = 346 := by kernel_rfl
theorem aa2_keep23 : rankKeep aa2 (35 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank23]
  decide +kernel
theorem aa2_rank24 : rank2 aa2 (36 / 1) = 350 := by kernel_rfl
theorem aa2_keep24 : rankKeep aa2 (36 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank24]
  decide +kernel
theorem aa2_rank25 : rank2 aa2 (40 / 1) = 354 := by kernel_rfl
theorem aa2_keep25 : rankKeep aa2 (40 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank25]
  decide +kernel
theorem aa2_rank26 : rank2 aa2 (44 / 1) = 358 := by kernel_rfl
theorem aa2_keep26 : rankKeep aa2 (44 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank26]
  decide +kernel
theorem aa2_rank27 : rank2 aa2 (45 / 1) = 363 := by kernel_rfl
theorem aa2_keep27 : rankKeep aa2 (45 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank27]
  decide +kernel
theorem aa2_rank28 : rank2 aa2 (50 / 1) = 366 := by kernel_rfl
theorem aa2_keep28 : rankKeep aa2 (50 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank28]
  decide +kernel
theorem aa2_rank29 : rank2 aa2 (54 / 1) = 368 := by kernel_rfl
theorem aa2_keep29 : rankKeep aa2 (54 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank29]
  decide +kernel
theorem aa2_rank30 : rank2 aa2 (56 / 1) = 370 := by kernel_rfl
theorem aa2_keep30 : rankKeep aa2 (56 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank30]
  decide +kernel
theorem aa2_rank31 : rank2 aa2 (58 / 1) = 372 := by kernel_rfl
theorem aa2_keep31 : rankKeep aa2 (58 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank31]
  decide +kernel
theorem aa2_rank32 : rank2 aa2 (60 / 1) = 376 := by kernel_rfl
theorem aa2_keep32 : rankKeep aa2 (60 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank32]
  decide +kernel
theorem aa2_rank33 : rank2 aa2 (63 / 1) = 380 := by kernel_rfl
theorem aa2_keep33 : rankKeep aa2 (63 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank33]
  decide +kernel
theorem aa2_rank34 : rank2 aa2 (64 / 1) = 382 := by kernel_rfl
theorem aa2_keep34 : rankKeep aa2 (64 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank34]
  decide +kernel
theorem aa2_rank35 : rank2 aa2 (65 / 1) = 384 := by kernel_rfl
theorem aa2_keep35 : rankKeep aa2 (65 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank35]
  decide +kernel
theorem aa2_rank36 : rank2 aa2 (68 / 1) = 386 := by kernel_rfl
theorem aa2_keep36 : rankKeep aa2 (68 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank36]
  decide +kernel
theorem aa2_rank37 : rank2 aa2 (69 / 1) = 388 := by kernel_rfl
theorem aa2_keep37 : rankKeep aa2 (69 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank37]
  decide +kernel
theorem aa2_rank38 : rank2 aa2 (70 / 1) = 390 := by kernel_rfl
theorem aa2_keep38 : rankKeep aa2 (70 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa2_length, aa2_rank38]
  decide +kernel
theorem aa2_rank39 : rank2 aa2 (77 / 1) = 392 := by kernel_rfl
theorem aa2_keep39 : rankKeep aa2 (77 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa2_length, aa2_rank39]
  decide +kernel
theorem aa2_rank40 : rank2 aa2 (80 / 1) = 395 := by kernel_rfl
theorem aa2_keep40 : rankKeep aa2 (80 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa2_length, aa2_rank40]
  decide +kernel
theorem aa2_rank41 : rank2 aa2 (81 / 1) = 398 := by kernel_rfl
theorem aa2_keep41 : rankKeep aa2 (81 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa2_length, aa2_rank41]
  decide +kernel
theorem aa2_rank42 : rank2 aa2 (110 / 1) = 400 := by kernel_rfl
theorem aa2_keep42 : rankKeep aa2 (110 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa2_length, aa2_rank42]
  decide +kernel
theorem aa2_rank43 : rank2 aa2 (117 / 1) = 402 := by kernel_rfl
theorem aa2_keep43 : rankKeep aa2 (117 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa2_length, aa2_rank43]
  decide +kernel
theorem aa2_rank44 : rank2 aa2 (126 / 1) = 404 := by kernel_rfl
theorem aa2_keep44 : rankKeep aa2 (126 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa2_length, aa2_rank44]
  decide +kernel
theorem aa2_rank45 : rank2 aa2 (140 / 1) = 406 := by kernel_rfl
theorem aa2_keep45 : rankKeep aa2 (140 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa2_length, aa2_rank45]
  decide +kernel
theorem aa2_rank46 : rank2 aa2 (150 / 1) = 408 := by kernel_rfl
theorem aa2_keep46 : rankKeep aa2 (150 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa2_length, aa2_rank46]
  decide +kernel
theorem aa2_rank47 : rank2 aa2 (176 / 1) = 410 := by kernel_rfl
theorem aa2_keep47 : rankKeep aa2 (176 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa2_length, aa2_rank47]
  decide +kernel
end Proofs.Witness
