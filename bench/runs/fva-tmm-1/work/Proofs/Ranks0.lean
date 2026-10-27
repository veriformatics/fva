import Proofs.WitnessData
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Proofs.Witness
def ps0 : List (Nat × Nat) := [(2, 2), (8, 10), (2, 2), (2, 2), (5, 4), (6, 4), (2, 2), (3, 3), (3, 3), (3, 3), (2, 2), (7, 5), (5, 5), (10, 9), (4, 5), (3, 3), (6, 4), (3, 3), (3, 2), (3, 3), (2, 2), (3, 2), (8, 5), (5, 3), (2, 2), (7, 4), (6, 4), (3, 2), (8, 9), (6, 6), (3, 3), (12, 8), (6, 7), (5, 6), (3, 2), (4, 3), (5, 5), (5, 6), (4, 5), (7, 5), (2, 2), (4, 4), (6, 5), (2, 2), (3, 3), (2, 2), (5, 4), (9, 7), (3, 3), (8, 9), (10, 6), (7, 4), (4, 3), (2, 2), (3, 2), (9, 6), (3, 2), (6, 5), (5, 4), (9, 6), (9, 6), (2, 2), (3, 3)]
def allps0 : List (Nat × Nat) := [(1, 4), (2, 2), (3, 1), (14, 4), (8, 10), (14, 9), (2, 2), (8, 3), (1, 2), (4, 8), (3, 4), (1, 1), (6, 3), (9, 16), (2, 2), (2, 1), (5, 4), (6, 4), (5, 9), (2, 11), (10, 2), (2, 2), (4, 2), (1, 1), (3, 3), (13, 1), (3, 3), (3, 3), (1, 1), (24, 6), (1, 2), (2, 2), (3, 1), (6, 1), (3, 1), (7, 5), (2, 1), (1, 1), (5, 7), (2, 1), (1, 7), (5, 5), (11, 3), (1, 2), (14, 1), (10, 9), (4, 5), (11, 25), (4, 1), (2, 3), (2, 11), (6, 9), (3, 3), (4, 12), (6, 2), (10, 12), (2, 1), (3, 17), (2, 3), (6, 4), (1, 3), (4, 2), (3, 3), (4, 2), (1, 9), (3, 2), (5, 2), (3, 3), (6, 2), (2, 2), (7, 3), (3, 1), (2, 1), (1, 2), (10, 19), (3, 1), (1, 3), (3, 2), (8, 5), (1, 2), (2, 1), (2, 1), (38, 16), (4, 1), (3, 1), (1, 4), (7, 3), (3, 7), (6, 16), (5, 3), (2, 2), (8, 13), (8, 2), (2, 1), (7, 4), (6, 4), (4, 1), (4, 1), (3, 2), (5, 9), (8, 29), (8, 9), (3, 8), (5, 9), (6, 6), (1, 1), (1, 1), (2, 1), (1, 1), (1, 2), (3, 4), (1, 1), (3, 3), (4, 1), (4, 2), (2, 4), (8, 1), (12, 3), (4, 1), (5, 1), (1, 1), (1, 1), (3, 1), (16, 1), (1, 3), (4, 2), (2, 1), (6, 1), (12, 8), (6, 7), (1, 2), (5, 6), (3, 2), (1, 1), (1, 1), (5, 2), (1, 1), (4, 3), (1, 1), (2, 8), (5, 5), (1, 1), (2, 3), (1, 2), (4, 13), (6, 2), (3, 1), (1, 1), (5, 6), (5, 11), (4, 1), (4, 5), (1, 2), (6, 2), (9, 2), (7, 5), (2, 1), (1, 2), (3, 10), (1, 1), (1, 2), (1, 1), (6, 23), (2, 2), (2, 1), (1, 1), (4, 4), (2, 4), (6, 5), (8, 2), (2, 2), (3, 3), (2, 2), (9, 4), (2, 6), (5, 4), (1, 1), (3, 5), (9, 3), (1, 4), (4, 10), (1, 1), (2, 3), (2, 3), (9, 3), (4, 9), (9, 7), (2, 1), (1, 2), (13, 8), (3, 3), (1, 1), (2, 3), (8, 9), (1, 2), (2, 4), (1, 1), (4, 1), (2, 1), (10, 6), (1, 4), (2, 5), (7, 1), (6, 11), (5, 2), (7, 4), (8, 3), (4, 3), (2, 1), (2, 9), (2, 2), (2, 1), (9, 3), (3, 2), (9, 6), (3, 10), (1, 5), (6, 1), (5, 11), (5, 10), (12, 9), (4, 2), (2, 1), (3, 2), (7, 3), (1, 2), (6, 5), (1, 2), (2, 1), (6, 1), (5, 4), (9, 6), (4, 7), (1, 1), (9, 6), (1, 2), (2, 2), (3, 3), (4, 1), (3, 1), (14, 10), (5, 9), (4, 2), (13, 1)]
def ms0 : List ℚ := [(1 / 4), (1 / 1), (3 / 1), (7 / 2), (4 / 5), (14 / 9), (1 / 1), (8 / 3), (1 / 2), (1 / 2), (3 / 4), (1 / 1), (2 / 1), (9 / 16), (1 / 1), (2 / 1), (5 / 4), (3 / 2), (5 / 9), (2 / 11), (5 / 1), (1 / 1), (2 / 1), (1 / 1), (1 / 1), (13 / 1), (1 / 1), (1 / 1), (1 / 1), (4 / 1), (1 / 2), (1 / 1), (3 / 1), (6 / 1), (3 / 1), (7 / 5), (2 / 1), (1 / 1), (5 / 7), (2 / 1), (1 / 7), (1 / 1), (11 / 3), (1 / 2), (14 / 1), (10 / 9), (4 / 5), (11 / 25), (4 / 1), (2 / 3), (2 / 11), (2 / 3), (1 / 1), (1 / 3), (3 / 1), (5 / 6), (2 / 1), (3 / 17), (2 / 3), (3 / 2), (1 / 3), (2 / 1), (1 / 1), (2 / 1), (1 / 9), (3 / 2), (5 / 2), (1 / 1), (3 / 1), (1 / 1), (7 / 3), (3 / 1), (2 / 1), (1 / 2), (10 / 19), (3 / 1), (1 / 3), (3 / 2), (8 / 5), (1 / 2), (2 / 1), (2 / 1), (19 / 8), (4 / 1), (3 / 1), (1 / 4), (7 / 3), (3 / 7), (3 / 8), (5 / 3), (1 / 1), (8 / 13), (4 / 1), (2 / 1), (7 / 4), (3 / 2), (4 / 1), (4 / 1), (3 / 2), (5 / 9), (8 / 29), (8 / 9), (3 / 8), (5 / 9), (1 / 1), (1 / 1), (1 / 1), (2 / 1), (1 / 1), (1 / 2), (3 / 4), (1 / 1), (1 / 1), (4 / 1), (2 / 1), (1 / 2), (8 / 1), (4 / 1), (4 / 1), (5 / 1), (1 / 1), (1 / 1), (3 / 1), (16 / 1), (1 / 3), (2 / 1), (2 / 1), (6 / 1), (3 / 2), (6 / 7), (1 / 2), (5 / 6), (3 / 2), (1 / 1), (1 / 1), (5 / 2), (1 / 1), (4 / 3), (1 / 1), (1 / 4), (1 / 1), (1 / 1), (2 / 3), (1 / 2), (4 / 13), (3 / 1), (3 / 1), (1 / 1), (5 / 6), (5 / 11), (4 / 1), (4 / 5), (1 / 2), (3 / 1), (9 / 2), (7 / 5), (2 / 1), (1 / 2), (3 / 10), (1 / 1), (1 / 2), (1 / 1), (6 / 23), (1 / 1), (2 / 1), (1 / 1), (1 / 1), (1 / 2), (6 / 5), (4 / 1), (1 / 1), (1 / 1), (1 / 1), (9 / 4), (1 / 3), (5 / 4), (1 / 1), (3 / 5), (3 / 1), (1 / 4), (2 / 5), (1 / 1), (2 / 3), (2 / 3), (3 / 1), (4 / 9), (9 / 7), (2 / 1), (1 / 2), (13 / 8), (1 / 1), (1 / 1), (2 / 3), (8 / 9), (1 / 2), (1 / 2), (1 / 1), (4 / 1), (2 / 1), (5 / 3), (1 / 4), (2 / 5), (7 / 1), (6 / 11), (5 / 2), (7 / 4), (8 / 3), (4 / 3), (2 / 1), (2 / 9), (1 / 1), (2 / 1), (3 / 1), (3 / 2), (3 / 2), (3 / 10), (1 / 5), (6 / 1), (5 / 11), (1 / 2), (4 / 3), (2 / 1), (2 / 1), (3 / 2), (7 / 3), (1 / 2), (6 / 5), (1 / 2), (2 / 1), (6 / 1), (5 / 4), (3 / 2), (4 / 7), (1 / 1), (3 / 2), (1 / 2), (1 / 1), (1 / 1), (4 / 1), (3 / 1), (7 / 5), (5 / 9), (2 / 1), (13 / 1)]
def aa0 : List ℚ := [4, 4, 3, 56, 80, 126, 4, 24, 2, 32, 12, 1, 18, 144, 4, 2, 20, 24, 45, 22, 20, 4, 8, 1, 9, 13, 9, 9, 1, 144, 2, 4, 3, 6, 3, 35, 2, 1, 35, 2, 7, 25, 33, 2, 14, 90, 20, 275, 4, 6, 22, 54, 9, 48, 12, 120, 2, 51, 6, 24, 3, 8, 9, 8, 9, 6, 10, 9, 12, 4, 21, 3, 2, 2, 190, 3, 3, 6, 40, 2, 2, 2, 608, 4, 3, 4, 21, 21, 96, 15, 4, 104, 16, 2, 28, 24, 4, 4, 6, 45, 232, 72, 24, 45, 36, 1, 1, 2, 1, 2, 12, 1, 9, 4, 8, 8, 8, 36, 4, 5, 1, 1, 3, 16, 3, 8, 2, 6, 96, 42, 2, 30, 6, 1, 1, 10, 1, 12, 1, 16, 25, 1, 6, 2, 52, 12, 3, 1, 30, 55, 4, 20, 2, 12, 18, 35, 2, 2, 30, 1, 2, 1, 138, 4, 2, 1, 16, 8, 30, 16, 4, 9, 4, 36, 12, 20, 1, 15, 27, 4, 40, 1, 6, 6, 27, 36, 63, 2, 2, 104, 9, 1, 6, 72, 2, 8, 1, 4, 2, 60, 4, 10, 7, 66, 10, 28, 24, 12, 2, 18, 4, 2, 27, 6, 54, 30, 5, 6, 55, 50, 108, 8, 2, 6, 21, 2, 30, 2, 2, 6, 20, 54, 28, 1, 54, 2, 4, 9, 4, 3, 140, 45, 8, 13]
theorem pairs0 : pairs matrix 0 3 = allps0 := by kernel_rfl
theorem ms_eq0 : allps0.map (fun p => (p.1 : ℚ) / p.2) = ms0 := by kernel_rfl
theorem aa_eq0 : allps0.map (fun p => ((p.1 * p.2 : Nat) : ℚ)) = aa0 := by kernel_rfl
theorem ms0_length : ms0.length = 244 := by kernel_rfl
theorem ms0_rank0 : rank2 ms0 (1 / 9) = 2 := by kernel_rfl
theorem ms0_keep0 : rankKeep ms0 (1 / 9) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank0]
  decide +kernel
theorem ms0_rank1 : rank2 ms0 (1 / 7) = 4 := by kernel_rfl
theorem ms0_keep1 : rankKeep ms0 (1 / 7) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank1]
  decide +kernel
theorem ms0_rank2 : rank2 ms0 (3 / 17) = 6 := by kernel_rfl
theorem ms0_keep2 : rankKeep ms0 (3 / 17) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank2]
  decide +kernel
theorem ms0_rank3 : rank2 ms0 (2 / 11) = 9 := by kernel_rfl
theorem ms0_keep3 : rankKeep ms0 (2 / 11) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank3]
  decide +kernel
theorem ms0_rank4 : rank2 ms0 (1 / 5) = 12 := by kernel_rfl
theorem ms0_keep4 : rankKeep ms0 (1 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank4]
  decide +kernel
theorem ms0_rank5 : rank2 ms0 (2 / 9) = 14 := by kernel_rfl
theorem ms0_keep5 : rankKeep ms0 (2 / 9) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank5]
  decide +kernel
theorem ms0_rank6 : rank2 ms0 (1 / 4) = 20 := by kernel_rfl
theorem ms0_keep6 : rankKeep ms0 (1 / 4) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank6]
  decide +kernel
theorem ms0_rank7 : rank2 ms0 (6 / 23) = 26 := by kernel_rfl
theorem ms0_keep7 : rankKeep ms0 (6 / 23) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank7]
  decide +kernel
theorem ms0_rank8 : rank2 ms0 (8 / 29) = 28 := by kernel_rfl
theorem ms0_keep8 : rankKeep ms0 (8 / 29) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank8]
  decide +kernel
theorem ms0_rank9 : rank2 ms0 (3 / 10) = 31 := by kernel_rfl
theorem ms0_keep9 : rankKeep ms0 (3 / 10) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank9]
  decide +kernel
theorem ms0_rank10 : rank2 ms0 (4 / 13) = 34 := by kernel_rfl
theorem ms0_keep10 : rankKeep ms0 (4 / 13) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank10]
  decide +kernel
theorem ms0_rank11 : rank2 ms0 (1 / 3) = 40 := by kernel_rfl
theorem ms0_keep11 : rankKeep ms0 (1 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank11]
  decide +kernel
theorem ms0_rank12 : rank2 ms0 (3 / 8) = 47 := by kernel_rfl
theorem ms0_keep12 : rankKeep ms0 (3 / 8) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank12]
  decide +kernel
theorem ms0_rank13 : rank2 ms0 (2 / 5) = 51 := by kernel_rfl
theorem ms0_keep13 : rankKeep ms0 (2 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank13]
  decide +kernel
theorem ms0_rank14 : rank2 ms0 (3 / 7) = 54 := by kernel_rfl
theorem ms0_keep14 : rankKeep ms0 (3 / 7) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank14]
  decide +kernel
theorem ms0_rank15 : rank2 ms0 (11 / 25) = 56 := by kernel_rfl
theorem ms0_keep15 : rankKeep ms0 (11 / 25) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank15]
  decide +kernel
theorem ms0_rank16 : rank2 ms0 (4 / 9) = 58 := by kernel_rfl
theorem ms0_keep16 : rankKeep ms0 (4 / 9) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank16]
  decide +kernel
theorem ms0_rank17 : rank2 ms0 (5 / 11) = 61 := by kernel_rfl
theorem ms0_keep17 : rankKeep ms0 (5 / 11) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank17]
  decide +kernel
theorem ms0_rank18 : rank2 ms0 (1 / 2) = 84 := by kernel_rfl
theorem ms0_keep18 : rankKeep ms0 (1 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank18]
  decide +kernel
theorem ms0_rank19 : rank2 ms0 (10 / 19) = 106 := by kernel_rfl
theorem ms0_keep19 : rankKeep ms0 (10 / 19) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank19]
  decide +kernel
theorem ms0_rank20 : rank2 ms0 (6 / 11) = 108 := by kernel_rfl
theorem ms0_keep20 : rankKeep ms0 (6 / 11) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank20]
  decide +kernel
theorem ms0_rank21 : rank2 ms0 (5 / 9) = 113 := by kernel_rfl
theorem ms0_keep21 : rankKeep ms0 (5 / 9) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank21]
  decide +kernel
theorem ms0_rank22 : rank2 ms0 (9 / 16) = 118 := by kernel_rfl
theorem ms0_keep22 : rankKeep ms0 (9 / 16) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank22]
  decide +kernel
theorem ms0_rank23 : rank2 ms0 (4 / 7) = 120 := by kernel_rfl
theorem ms0_keep23 : rankKeep ms0 (4 / 7) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank23]
  decide +kernel
theorem ms0_rank24 : rank2 ms0 (3 / 5) = 122 := by kernel_rfl
theorem ms0_keep24 : rankKeep ms0 (3 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank24]
  decide +kernel
theorem ms0_rank25 : rank2 ms0 (8 / 13) = 124 := by kernel_rfl
theorem ms0_keep25 : rankKeep ms0 (8 / 13) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank25]
  decide +kernel
theorem ms0_rank26 : rank2 ms0 (2 / 3) = 132 := by kernel_rfl
theorem ms0_keep26 : rankKeep ms0 (2 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank26]
  decide +kernel
theorem ms0_rank27 : rank2 ms0 (5 / 7) = 140 := by kernel_rfl
theorem ms0_keep27 : rankKeep ms0 (5 / 7) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank27]
  decide +kernel
theorem ms0_rank28 : rank2 ms0 (3 / 4) = 143 := by kernel_rfl
theorem ms0_keep28 : rankKeep ms0 (3 / 4) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank28]
  decide +kernel
theorem ms0_rank29 : rank2 ms0 (4 / 5) = 148 := by kernel_rfl
theorem ms0_keep29 : rankKeep ms0 (4 / 5) 3 10 = true := by
  unfold rankKeep
  rw [ms0_length, ms0_rank29]
  decide +kernel
theorem ms0_rank30 : rank2 ms0 (5 / 6) = 154 := by kernel_rfl
theorem ms0_keep30 : rankKeep ms0 (5 / 6) 3 10 = true := by
  unfold rankKeep
  rw [ms0_length, ms0_rank30]
  decide +kernel
theorem ms0_rank31 : rank2 ms0 (6 / 7) = 158 := by kernel_rfl
theorem ms0_keep31 : rankKeep ms0 (6 / 7) 3 10 = true := by
  unfold rankKeep
  rw [ms0_length, ms0_rank31]
  decide +kernel
theorem ms0_rank32 : rank2 ms0 (8 / 9) = 161 := by kernel_rfl
theorem ms0_keep32 : rankKeep ms0 (8 / 9) 3 10 = true := by
  unfold rankKeep
  rw [ms0_length, ms0_rank32]
  decide +kernel
theorem ms0_rank33 : rank2 ms0 (1 / 1) = 213 := by kernel_rfl
theorem ms0_keep33 : rankKeep ms0 (1 / 1) 3 10 = true := by
  unfold rankKeep
  rw [ms0_length, ms0_rank33]
  decide +kernel
theorem ms0_rank34 : rank2 ms0 (10 / 9) = 264 := by kernel_rfl
theorem ms0_keep34 : rankKeep ms0 (10 / 9) 3 10 = true := by
  unfold rankKeep
  rw [ms0_length, ms0_rank34]
  decide +kernel
theorem ms0_rank35 : rank2 ms0 (6 / 5) = 267 := by kernel_rfl
theorem ms0_keep35 : rankKeep ms0 (6 / 5) 3 10 = true := by
  unfold rankKeep
  rw [ms0_length, ms0_rank35]
  decide +kernel
theorem ms0_rank36 : rank2 ms0 (5 / 4) = 272 := by kernel_rfl
theorem ms0_keep36 : rankKeep ms0 (5 / 4) 3 10 = true := by
  unfold rankKeep
  rw [ms0_length, ms0_rank36]
  decide +kernel
theorem ms0_rank37 : rank2 ms0 (9 / 7) = 276 := by kernel_rfl
theorem ms0_keep37 : rankKeep ms0 (9 / 7) 3 10 = true := by
  unfold rankKeep
  rw [ms0_length, ms0_rank37]
  decide +kernel
theorem ms0_rank38 : rank2 ms0 (4 / 3) = 280 := by kernel_rfl
theorem ms0_keep38 : rankKeep ms0 (4 / 3) 3 10 = true := by
  unfold rankKeep
  rw [ms0_length, ms0_rank38]
  decide +kernel
theorem ms0_rank39 : rank2 ms0 (7 / 5) = 286 := by kernel_rfl
theorem ms0_keep39 : rankKeep ms0 (7 / 5) 3 10 = true := by
  unfold rankKeep
  rw [ms0_length, ms0_rank39]
  decide +kernel
theorem ms0_rank40 : rank2 ms0 (3 / 2) = 302 := by kernel_rfl
theorem ms0_keep40 : rankKeep ms0 (3 / 2) 3 10 = true := by
  unfold rankKeep
  rw [ms0_length, ms0_rank40]
  decide +kernel
theorem ms0_rank41 : rank2 ms0 (14 / 9) = 316 := by kernel_rfl
theorem ms0_keep41 : rankKeep ms0 (14 / 9) 3 10 = true := by
  unfold rankKeep
  rw [ms0_length, ms0_rank41]
  decide +kernel
theorem ms0_rank42 : rank2 ms0 (8 / 5) = 318 := by kernel_rfl
theorem ms0_keep42 : rankKeep ms0 (8 / 5) 3 10 = true := by
  unfold rankKeep
  rw [ms0_length, ms0_rank42]
  decide +kernel
theorem ms0_rank43 : rank2 ms0 (13 / 8) = 320 := by kernel_rfl
theorem ms0_keep43 : rankKeep ms0 (13 / 8) 3 10 = true := by
  unfold rankKeep
  rw [ms0_length, ms0_rank43]
  decide +kernel
theorem ms0_rank44 : rank2 ms0 (5 / 3) = 323 := by kernel_rfl
theorem ms0_keep44 : rankKeep ms0 (5 / 3) 3 10 = true := by
  unfold rankKeep
  rw [ms0_length, ms0_rank44]
  decide +kernel
theorem ms0_rank45 : rank2 ms0 (7 / 4) = 327 := by kernel_rfl
theorem ms0_keep45 : rankKeep ms0 (7 / 4) 3 10 = true := by
  unfold rankKeep
  rw [ms0_length, ms0_rank45]
  decide +kernel
theorem ms0_rank46 : rank2 ms0 (2 / 1) = 355 := by kernel_rfl
theorem ms0_keep46 : rankKeep ms0 (2 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank46]
  decide +kernel
theorem ms0_rank47 : rank2 ms0 (9 / 4) = 382 := by kernel_rfl
theorem ms0_keep47 : rankKeep ms0 (9 / 4) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank47]
  decide +kernel
theorem ms0_rank48 : rank2 ms0 (7 / 3) = 386 := by kernel_rfl
theorem ms0_keep48 : rankKeep ms0 (7 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank48]
  decide +kernel
theorem ms0_rank49 : rank2 ms0 (19 / 8) = 390 := by kernel_rfl
theorem ms0_keep49 : rankKeep ms0 (19 / 8) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank49]
  decide +kernel
theorem ms0_rank50 : rank2 ms0 (5 / 2) = 394 := by kernel_rfl
theorem ms0_keep50 : rankKeep ms0 (5 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank50]
  decide +kernel
theorem ms0_rank51 : rank2 ms0 (8 / 3) = 399 := by kernel_rfl
theorem ms0_keep51 : rankKeep ms0 (8 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank51]
  decide +kernel
theorem ms0_rank52 : rank2 ms0 (3 / 1) = 417 := by kernel_rfl
theorem ms0_keep52 : rankKeep ms0 (3 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank52]
  decide +kernel
theorem ms0_rank53 : rank2 ms0 (7 / 2) = 434 := by kernel_rfl
theorem ms0_keep53 : rankKeep ms0 (7 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank53]
  decide +kernel
theorem ms0_rank54 : rank2 ms0 (11 / 3) = 436 := by kernel_rfl
theorem ms0_keep54 : rankKeep ms0 (11 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank54]
  decide +kernel
theorem ms0_rank55 : rank2 ms0 (4 / 1) = 450 := by kernel_rfl
theorem ms0_keep55 : rankKeep ms0 (4 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank55]
  decide +kernel
theorem ms0_rank56 : rank2 ms0 (9 / 2) = 464 := by kernel_rfl
theorem ms0_keep56 : rankKeep ms0 (9 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank56]
  decide +kernel
theorem ms0_rank57 : rank2 ms0 (5 / 1) = 467 := by kernel_rfl
theorem ms0_keep57 : rankKeep ms0 (5 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank57]
  decide +kernel
theorem ms0_rank58 : rank2 ms0 (6 / 1) = 473 := by kernel_rfl
theorem ms0_keep58 : rankKeep ms0 (6 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank58]
  decide +kernel
theorem ms0_rank59 : rank2 ms0 (7 / 1) = 478 := by kernel_rfl
theorem ms0_keep59 : rankKeep ms0 (7 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank59]
  decide +kernel
theorem ms0_rank60 : rank2 ms0 (8 / 1) = 480 := by kernel_rfl
theorem ms0_keep60 : rankKeep ms0 (8 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank60]
  decide +kernel
theorem ms0_rank61 : rank2 ms0 (13 / 1) = 483 := by kernel_rfl
theorem ms0_keep61 : rankKeep ms0 (13 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank61]
  decide +kernel
theorem ms0_rank62 : rank2 ms0 (14 / 1) = 486 := by kernel_rfl
theorem ms0_keep62 : rankKeep ms0 (14 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank62]
  decide +kernel
theorem ms0_rank63 : rank2 ms0 (16 / 1) = 488 := by kernel_rfl
theorem ms0_keep63 : rankKeep ms0 (16 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms0_length, ms0_rank63]
  decide +kernel
theorem aa0_length : aa0.length = 244 := by kernel_rfl
theorem aa0_rank0 : rank2 aa0 (1 / 1) = 25 := by kernel_rfl
theorem aa0_keep0 : rankKeep aa0 (1 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa0_length, aa0_rank0]
  decide +kernel
theorem aa0_rank1 : rank2 aa0 (2 / 1) = 83 := by kernel_rfl
theorem aa0_keep1 : rankKeep aa0 (2 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank1]
  decide +kernel
theorem aa0_rank2 : rank2 aa0 (3 / 1) = 129 := by kernel_rfl
theorem aa0_keep2 : rankKeep aa0 (3 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank2]
  decide +kernel
theorem aa0_rank3 : rank2 aa0 (4 / 1) = 166 := by kernel_rfl
theorem aa0_keep3 : rankKeep aa0 (4 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank3]
  decide +kernel
theorem aa0_rank4 : rank2 aa0 (5 / 1) = 193 := by kernel_rfl
theorem aa0_keep4 : rankKeep aa0 (5 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank4]
  decide +kernel
theorem aa0_rank5 : rank2 aa0 (6 / 1) = 211 := by kernel_rfl
theorem aa0_keep5 : rankKeep aa0 (6 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank5]
  decide +kernel
theorem aa0_rank6 : rank2 aa0 (7 / 1) = 229 := by kernel_rfl
theorem aa0_keep6 : rankKeep aa0 (7 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank6]
  decide +kernel
theorem aa0_rank7 : rank2 aa0 (8 / 1) = 242 := by kernel_rfl
theorem aa0_keep7 : rankKeep aa0 (8 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank7]
  decide +kernel
theorem aa0_rank8 : rank2 aa0 (9 / 1) = 264 := by kernel_rfl
theorem aa0_keep8 : rankKeep aa0 (9 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank8]
  decide +kernel
theorem aa0_rank9 : rank2 aa0 (10 / 1) = 279 := by kernel_rfl
theorem aa0_keep9 : rankKeep aa0 (10 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank9]
  decide +kernel
theorem aa0_rank10 : rank2 aa0 (12 / 1) = 292 := by kernel_rfl
theorem aa0_keep10 : rankKeep aa0 (12 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank10]
  decide +kernel
theorem aa0_rank11 : rank2 aa0 (13 / 1) = 303 := by kernel_rfl
theorem aa0_keep11 : rankKeep aa0 (13 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank11]
  decide +kernel
theorem aa0_rank12 : rank2 aa0 (14 / 1) = 306 := by kernel_rfl
theorem aa0_keep12 : rankKeep aa0 (14 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank12]
  decide +kernel
theorem aa0_rank13 : rank2 aa0 (15 / 1) = 309 := by kernel_rfl
theorem aa0_keep13 : rankKeep aa0 (15 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank13]
  decide +kernel
theorem aa0_rank14 : rank2 aa0 (16 / 1) = 316 := by kernel_rfl
theorem aa0_keep14 : rankKeep aa0 (16 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank14]
  decide +kernel
theorem aa0_rank15 : rank2 aa0 (18 / 1) = 324 := by kernel_rfl
theorem aa0_keep15 : rankKeep aa0 (18 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank15]
  decide +kernel
theorem aa0_rank16 : rank2 aa0 (20 / 1) = 333 := by kernel_rfl
theorem aa0_keep16 : rankKeep aa0 (20 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank16]
  decide +kernel
theorem aa0_rank17 : rank2 aa0 (21 / 1) = 343 := by kernel_rfl
theorem aa0_keep17 : rankKeep aa0 (21 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank17]
  decide +kernel
theorem aa0_rank18 : rank2 aa0 (22 / 1) = 349 := by kernel_rfl
theorem aa0_keep18 : rankKeep aa0 (22 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank18]
  decide +kernel
theorem aa0_rank19 : rank2 aa0 (24 / 1) = 357 := by kernel_rfl
theorem aa0_keep19 : rankKeep aa0 (24 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank19]
  decide +kernel
theorem aa0_rank20 : rank2 aa0 (25 / 1) = 365 := by kernel_rfl
theorem aa0_keep20 : rankKeep aa0 (25 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank20]
  decide +kernel
theorem aa0_rank21 : rank2 aa0 (27 / 1) = 370 := by kernel_rfl
theorem aa0_keep21 : rankKeep aa0 (27 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank21]
  decide +kernel
theorem aa0_rank22 : rank2 aa0 (28 / 1) = 376 := by kernel_rfl
theorem aa0_keep22 : rankKeep aa0 (28 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank22]
  decide +kernel
theorem aa0_rank23 : rank2 aa0 (30 / 1) = 385 := by kernel_rfl
theorem aa0_keep23 : rankKeep aa0 (30 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank23]
  decide +kernel
theorem aa0_rank24 : rank2 aa0 (32 / 1) = 392 := by kernel_rfl
theorem aa0_keep24 : rankKeep aa0 (32 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank24]
  decide +kernel
theorem aa0_rank25 : rank2 aa0 (33 / 1) = 394 := by kernel_rfl
theorem aa0_keep25 : rankKeep aa0 (33 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank25]
  decide +kernel
theorem aa0_rank26 : rank2 aa0 (35 / 1) = 398 := by kernel_rfl
theorem aa0_keep26 : rankKeep aa0 (35 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank26]
  decide +kernel
theorem aa0_rank27 : rank2 aa0 (36 / 1) = 405 := by kernel_rfl
theorem aa0_keep27 : rankKeep aa0 (36 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank27]
  decide +kernel
theorem aa0_rank28 : rank2 aa0 (40 / 1) = 411 := by kernel_rfl
theorem aa0_keep28 : rankKeep aa0 (40 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank28]
  decide +kernel
theorem aa0_rank29 : rank2 aa0 (42 / 1) = 414 := by kernel_rfl
theorem aa0_keep29 : rankKeep aa0 (42 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank29]
  decide +kernel
theorem aa0_rank30 : rank2 aa0 (45 / 1) = 419 := by kernel_rfl
theorem aa0_keep30 : rankKeep aa0 (45 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank30]
  decide +kernel
theorem aa0_rank31 : rank2 aa0 (48 / 1) = 424 := by kernel_rfl
theorem aa0_keep31 : rankKeep aa0 (48 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank31]
  decide +kernel
theorem aa0_rank32 : rank2 aa0 (50 / 1) = 426 := by kernel_rfl
theorem aa0_keep32 : rankKeep aa0 (50 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank32]
  decide +kernel
theorem aa0_rank33 : rank2 aa0 (51 / 1) = 428 := by kernel_rfl
theorem aa0_keep33 : rankKeep aa0 (51 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank33]
  decide +kernel
theorem aa0_rank34 : rank2 aa0 (52 / 1) = 430 := by kernel_rfl
theorem aa0_keep34 : rankKeep aa0 (52 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank34]
  decide +kernel
theorem aa0_rank35 : rank2 aa0 (54 / 1) = 435 := by kernel_rfl
theorem aa0_keep35 : rankKeep aa0 (54 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank35]
  decide +kernel
theorem aa0_rank36 : rank2 aa0 (55 / 1) = 441 := by kernel_rfl
theorem aa0_keep36 : rankKeep aa0 (55 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank36]
  decide +kernel
theorem aa0_rank37 : rank2 aa0 (56 / 1) = 444 := by kernel_rfl
theorem aa0_keep37 : rankKeep aa0 (56 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank37]
  decide +kernel
theorem aa0_rank38 : rank2 aa0 (60 / 1) = 446 := by kernel_rfl
theorem aa0_keep38 : rankKeep aa0 (60 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank38]
  decide +kernel
theorem aa0_rank39 : rank2 aa0 (63 / 1) = 448 := by kernel_rfl
theorem aa0_keep39 : rankKeep aa0 (63 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank39]
  decide +kernel
theorem aa0_rank40 : rank2 aa0 (66 / 1) = 450 := by kernel_rfl
theorem aa0_keep40 : rankKeep aa0 (66 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank40]
  decide +kernel
theorem aa0_rank41 : rank2 aa0 (72 / 1) = 453 := by kernel_rfl
theorem aa0_keep41 : rankKeep aa0 (72 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank41]
  decide +kernel
theorem aa0_rank42 : rank2 aa0 (80 / 1) = 456 := by kernel_rfl
theorem aa0_keep42 : rankKeep aa0 (80 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank42]
  decide +kernel
theorem aa0_rank43 : rank2 aa0 (90 / 1) = 458 := by kernel_rfl
theorem aa0_keep43 : rankKeep aa0 (90 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank43]
  decide +kernel
theorem aa0_rank44 : rank2 aa0 (96 / 1) = 461 := by kernel_rfl
theorem aa0_keep44 : rankKeep aa0 (96 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa0_length, aa0_rank44]
  decide +kernel
theorem aa0_rank45 : rank2 aa0 (104 / 1) = 465 := by kernel_rfl
theorem aa0_keep45 : rankKeep aa0 (104 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa0_length, aa0_rank45]
  decide +kernel
theorem aa0_rank46 : rank2 aa0 (108 / 1) = 468 := by kernel_rfl
theorem aa0_keep46 : rankKeep aa0 (108 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa0_length, aa0_rank46]
  decide +kernel
theorem aa0_rank47 : rank2 aa0 (120 / 1) = 470 := by kernel_rfl
theorem aa0_keep47 : rankKeep aa0 (120 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa0_length, aa0_rank47]
  decide +kernel
theorem aa0_rank48 : rank2 aa0 (126 / 1) = 472 := by kernel_rfl
theorem aa0_keep48 : rankKeep aa0 (126 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa0_length, aa0_rank48]
  decide +kernel
theorem aa0_rank49 : rank2 aa0 (138 / 1) = 474 := by kernel_rfl
theorem aa0_keep49 : rankKeep aa0 (138 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa0_length, aa0_rank49]
  decide +kernel
theorem aa0_rank50 : rank2 aa0 (140 / 1) = 476 := by kernel_rfl
theorem aa0_keep50 : rankKeep aa0 (140 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa0_length, aa0_rank50]
  decide +kernel
theorem aa0_rank51 : rank2 aa0 (144 / 1) = 479 := by kernel_rfl
theorem aa0_keep51 : rankKeep aa0 (144 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa0_length, aa0_rank51]
  decide +kernel
theorem aa0_rank52 : rank2 aa0 (190 / 1) = 482 := by kernel_rfl
theorem aa0_keep52 : rankKeep aa0 (190 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa0_length, aa0_rank52]
  decide +kernel
theorem aa0_rank53 : rank2 aa0 (232 / 1) = 484 := by kernel_rfl
theorem aa0_keep53 : rankKeep aa0 (232 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa0_length, aa0_rank53]
  decide +kernel
theorem aa0_rank54 : rank2 aa0 (275 / 1) = 486 := by kernel_rfl
theorem aa0_keep54 : rankKeep aa0 (275 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa0_length, aa0_rank54]
  decide +kernel
theorem aa0_rank55 : rank2 aa0 (608 / 1) = 488 := by kernel_rfl
theorem aa0_keep55 : rankKeep aa0 (608 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa0_length, aa0_rank55]
  decide +kernel
end Proofs.Witness
