import Proofs.WitnessData
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Proofs.Witness
def ps6 : List (Nat × Nat) := [(7, 4), (4, 3), (3, 2), (3, 2), (4, 4), (1, 1), (1, 1), (7, 4), (1, 1), (5, 3), (2, 2), (6, 5), (1, 1), (6, 7), (3, 2), (2, 2), (1, 1), (7, 9), (1, 1), (3, 3), (2, 2), (2, 2), (5, 3), (1, 1), (8, 5), (1, 1), (3, 3), (2, 2), (1, 1), (3, 2), (7, 9), (2, 2), (4, 4), (1, 1), (5, 3), (3, 4), (1, 1), (7, 7), (5, 5), (10, 8), (2, 2), (2, 2), (1, 1), (9, 6), (2, 2), (1, 1), (3, 2), (1, 1), (2, 2), (1, 1), (1, 1), (1, 1), (4, 3), (1, 1), (6, 6), (1, 1), (7, 5), (1, 1), (5, 5), (3, 2), (3, 4), (1, 1), (3, 2), (4, 4), (1, 1), (3, 3), (8, 9), (2, 2), (6, 6), (1, 1), (1, 1), (7, 9), (2, 2), (1, 1), (5, 3), (1, 1), (5, 5), (5, 4), (5, 3)]
def allps6 : List (Nat × Nat) := [(7, 4), (11, 1), (4, 7), (16, 4), (24, 10), (3, 9), (4, 3), (3, 2), (1, 8), (3, 2), (4, 4), (1, 1), (3, 1), (9, 3), (15, 16), (1, 1), (7, 4), (1, 4), (3, 9), (8, 11), (1, 2), (1, 1), (5, 3), (2, 3), (2, 3), (4, 6), (2, 2), (7, 1), (2, 1), (2, 1), (6, 5), (2, 1), (3, 7), (1, 1), (6, 7), (3, 2), (2, 5), (2, 2), (8, 1), (6, 9), (2, 5), (4, 25), (1, 1), (7, 9), (2, 3), (1, 1), (1, 12), (6, 2), (2, 1), (16, 12), (4, 1), (14, 17), (3, 3), (26, 4), (1, 3), (2, 2), (2, 1), (6, 2), (3, 9), (8, 2), (11, 2), (2, 3), (2, 3), (2, 2), (1, 2), (5, 3), (1, 1), (5, 19), (2, 3), (4, 2), (8, 5), (4, 2), (3, 1), (4, 1), (37, 16), (1, 1), (3, 3), (17, 7), (22, 16), (7, 3), (3, 13), (2, 1), (2, 2), (3, 1), (2, 4), (1, 4), (1, 1), (2, 1), (3, 2), (7, 9), (6, 29), (13, 9), (1, 8), (1, 9), (4, 6), (2, 2), (1, 5), (2, 1), (3, 1), (4, 4), (1, 1), (5, 3), (3, 1), (14, 2), (3, 4), (8, 1), (13, 3), (11, 1), (2, 1), (1, 1), (2, 1), (3, 1), (1, 3), (11, 2), (8, 1), (2, 8), (7, 7), (3, 6), (5, 2), (8, 1), (3, 1), (7, 3), (5, 5), (10, 8), (2, 5), (5, 1), (8, 3), (2, 2), (2, 13), (2, 2), (9, 1), (1, 1), (9, 6), (1, 11), (3, 1), (3, 5), (2, 1), (1, 2), (2, 2), (6, 2), (1, 1), (2, 5), (3, 2), (1, 1), (2, 2), (1, 1), (3, 23), (1, 1), (6, 2), (1, 1), (3, 1), (1, 4), (2, 4), (9, 2), (4, 3), (1, 1), (4, 2), (20, 4), (6, 6), (9, 1), (1, 1), (7, 5), (10, 3), (5, 10), (1, 1), (10, 3), (6, 3), (6, 9), (5, 5), (2, 1), (3, 2), (23, 8), (2, 5), (1, 3), (1, 3), (4, 9), (3, 4), (1, 1), (6, 1), (3, 2), (1, 6), (4, 4), (1, 2), (4, 1), (2, 5), (2, 11), (1, 4), (8, 2), (1, 1), (1, 4), (3, 3), (2, 3), (4, 1), (8, 9), (2, 1), (1, 2), (6, 3), (2, 2), (6, 6), (1, 1), (1, 10), (2, 5), (1, 1), (10, 5), (8, 11), (1, 10), (7, 9), (2, 2), (1, 1), (1, 2), (5, 3), (1, 1), (5, 5), (1, 2), (3, 1), (5, 4), (2, 6), (2, 1), (4, 7), (14, 6), (1, 2), (4, 2), (5, 3), (2, 1), (6, 10), (2, 9), (2, 1)]
def ms6 : List ℚ := [(7 / 4), (11 / 1), (4 / 7), (4 / 1), (12 / 5), (1 / 3), (4 / 3), (3 / 2), (1 / 8), (3 / 2), (1 / 1), (1 / 1), (3 / 1), (3 / 1), (15 / 16), (1 / 1), (7 / 4), (1 / 4), (1 / 3), (8 / 11), (1 / 2), (1 / 1), (5 / 3), (2 / 3), (2 / 3), (2 / 3), (1 / 1), (7 / 1), (2 / 1), (2 / 1), (6 / 5), (2 / 1), (3 / 7), (1 / 1), (6 / 7), (3 / 2), (2 / 5), (1 / 1), (8 / 1), (2 / 3), (2 / 5), (4 / 25), (1 / 1), (7 / 9), (2 / 3), (1 / 1), (1 / 12), (3 / 1), (2 / 1), (4 / 3), (4 / 1), (14 / 17), (1 / 1), (13 / 2), (1 / 3), (1 / 1), (2 / 1), (3 / 1), (1 / 3), (4 / 1), (11 / 2), (2 / 3), (2 / 3), (1 / 1), (1 / 2), (5 / 3), (1 / 1), (5 / 19), (2 / 3), (2 / 1), (8 / 5), (2 / 1), (3 / 1), (4 / 1), (37 / 16), (1 / 1), (1 / 1), (17 / 7), (11 / 8), (7 / 3), (3 / 13), (2 / 1), (1 / 1), (3 / 1), (1 / 2), (1 / 4), (1 / 1), (2 / 1), (3 / 2), (7 / 9), (6 / 29), (13 / 9), (1 / 8), (1 / 9), (2 / 3), (1 / 1), (1 / 5), (2 / 1), (3 / 1), (1 / 1), (1 / 1), (5 / 3), (3 / 1), (7 / 1), (3 / 4), (8 / 1), (13 / 3), (11 / 1), (2 / 1), (1 / 1), (2 / 1), (3 / 1), (1 / 3), (11 / 2), (8 / 1), (1 / 4), (1 / 1), (1 / 2), (5 / 2), (8 / 1), (3 / 1), (7 / 3), (1 / 1), (5 / 4), (2 / 5), (5 / 1), (8 / 3), (1 / 1), (2 / 13), (1 / 1), (9 / 1), (1 / 1), (3 / 2), (1 / 11), (3 / 1), (3 / 5), (2 / 1), (1 / 2), (1 / 1), (3 / 1), (1 / 1), (2 / 5), (3 / 2), (1 / 1), (1 / 1), (1 / 1), (3 / 23), (1 / 1), (3 / 1), (1 / 1), (3 / 1), (1 / 4), (1 / 2), (9 / 2), (4 / 3), (1 / 1), (2 / 1), (5 / 1), (1 / 1), (9 / 1), (1 / 1), (7 / 5), (10 / 3), (1 / 2), (1 / 1), (10 / 3), (2 / 1), (2 / 3), (1 / 1), (2 / 1), (3 / 2), (23 / 8), (2 / 5), (1 / 3), (1 / 3), (4 / 9), (3 / 4), (1 / 1), (6 / 1), (3 / 2), (1 / 6), (1 / 1), (1 / 2), (4 / 1), (2 / 5), (2 / 11), (1 / 4), (4 / 1), (1 / 1), (1 / 4), (1 / 1), (2 / 3), (4 / 1), (8 / 9), (2 / 1), (1 / 2), (2 / 1), (1 / 1), (1 / 1), (1 / 1), (1 / 10), (2 / 5), (1 / 1), (2 / 1), (8 / 11), (1 / 10), (7 / 9), (1 / 1), (1 / 1), (1 / 2), (5 / 3), (1 / 1), (1 / 1), (1 / 2), (3 / 1), (5 / 4), (1 / 3), (2 / 1), (4 / 7), (7 / 3), (1 / 2), (2 / 1), (5 / 3), (2 / 1), (3 / 5), (2 / 9), (2 / 1)]
def aa6 : List ℚ := [28, 11, 28, 64, 240, 27, 12, 6, 8, 6, 16, 1, 3, 27, 240, 1, 28, 4, 27, 88, 2, 1, 15, 6, 6, 24, 4, 7, 2, 2, 30, 2, 21, 1, 42, 6, 10, 4, 8, 54, 10, 100, 1, 63, 6, 1, 12, 12, 2, 192, 4, 238, 9, 104, 3, 4, 2, 12, 27, 16, 22, 6, 6, 4, 2, 15, 1, 95, 6, 8, 40, 8, 3, 4, 592, 1, 9, 119, 352, 21, 39, 2, 4, 3, 8, 4, 1, 2, 6, 63, 174, 117, 8, 9, 24, 4, 5, 2, 3, 16, 1, 15, 3, 28, 12, 8, 39, 11, 2, 1, 2, 3, 3, 22, 8, 16, 49, 18, 10, 8, 3, 21, 25, 80, 10, 5, 24, 4, 26, 4, 9, 1, 54, 11, 3, 15, 2, 2, 4, 12, 1, 10, 6, 1, 4, 1, 69, 1, 12, 1, 3, 4, 8, 18, 12, 1, 8, 80, 36, 9, 1, 35, 30, 50, 1, 30, 18, 54, 25, 2, 6, 184, 10, 3, 3, 36, 12, 1, 6, 6, 6, 16, 2, 4, 10, 22, 4, 16, 1, 4, 9, 6, 4, 72, 2, 2, 18, 4, 36, 1, 10, 10, 1, 50, 88, 10, 63, 4, 1, 2, 15, 1, 25, 2, 3, 20, 12, 2, 28, 84, 2, 8, 15, 2, 60, 18, 2]
theorem pairs6 : pairs matrix 6 3 = allps6 := by kernel_rfl
theorem ms_eq6 : allps6.map (fun p => (p.1 : ℚ) / p.2) = ms6 := by kernel_rfl
theorem aa_eq6 : allps6.map (fun p => ((p.1 * p.2 : Nat) : ℚ)) = aa6 := by kernel_rfl
theorem ms6_length : ms6.length = 227 := by kernel_rfl
theorem ms6_rank0 : rank2 ms6 (1 / 12) = 2 := by kernel_rfl
theorem ms6_keep0 : rankKeep ms6 (1 / 12) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank0]
  decide +kernel
theorem ms6_rank1 : rank2 ms6 (1 / 11) = 4 := by kernel_rfl
theorem ms6_keep1 : rankKeep ms6 (1 / 11) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank1]
  decide +kernel
theorem ms6_rank2 : rank2 ms6 (1 / 10) = 7 := by kernel_rfl
theorem ms6_keep2 : rankKeep ms6 (1 / 10) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank2]
  decide +kernel
theorem ms6_rank3 : rank2 ms6 (1 / 9) = 10 := by kernel_rfl
theorem ms6_keep3 : rankKeep ms6 (1 / 9) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank3]
  decide +kernel
theorem ms6_rank4 : rank2 ms6 (1 / 8) = 13 := by kernel_rfl
theorem ms6_keep4 : rankKeep ms6 (1 / 8) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank4]
  decide +kernel
theorem ms6_rank5 : rank2 ms6 (3 / 23) = 16 := by kernel_rfl
theorem ms6_keep5 : rankKeep ms6 (3 / 23) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank5]
  decide +kernel
theorem ms6_rank6 : rank2 ms6 (2 / 13) = 18 := by kernel_rfl
theorem ms6_keep6 : rankKeep ms6 (2 / 13) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank6]
  decide +kernel
theorem ms6_rank7 : rank2 ms6 (4 / 25) = 20 := by kernel_rfl
theorem ms6_keep7 : rankKeep ms6 (4 / 25) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank7]
  decide +kernel
theorem ms6_rank8 : rank2 ms6 (1 / 6) = 22 := by kernel_rfl
theorem ms6_keep8 : rankKeep ms6 (1 / 6) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank8]
  decide +kernel
theorem ms6_rank9 : rank2 ms6 (2 / 11) = 24 := by kernel_rfl
theorem ms6_keep9 : rankKeep ms6 (2 / 11) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank9]
  decide +kernel
theorem ms6_rank10 : rank2 ms6 (1 / 5) = 26 := by kernel_rfl
theorem ms6_keep10 : rankKeep ms6 (1 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank10]
  decide +kernel
theorem ms6_rank11 : rank2 ms6 (6 / 29) = 28 := by kernel_rfl
theorem ms6_keep11 : rankKeep ms6 (6 / 29) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank11]
  decide +kernel
theorem ms6_rank12 : rank2 ms6 (2 / 9) = 30 := by kernel_rfl
theorem ms6_keep12 : rankKeep ms6 (2 / 9) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank12]
  decide +kernel
theorem ms6_rank13 : rank2 ms6 (3 / 13) = 32 := by kernel_rfl
theorem ms6_keep13 : rankKeep ms6 (3 / 13) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank13]
  decide +kernel
theorem ms6_rank14 : rank2 ms6 (1 / 4) = 39 := by kernel_rfl
theorem ms6_keep14 : rankKeep ms6 (1 / 4) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank14]
  decide +kernel
theorem ms6_rank15 : rank2 ms6 (5 / 19) = 46 := by kernel_rfl
theorem ms6_keep15 : rankKeep ms6 (5 / 19) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank15]
  decide +kernel
theorem ms6_rank16 : rank2 ms6 (1 / 3) = 55 := by kernel_rfl
theorem ms6_keep16 : rankKeep ms6 (1 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank16]
  decide +kernel
theorem ms6_rank17 : rank2 ms6 (2 / 5) = 70 := by kernel_rfl
theorem ms6_keep17 : rankKeep ms6 (2 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank17]
  decide +kernel
theorem ms6_rank18 : rank2 ms6 (3 / 7) = 78 := by kernel_rfl
theorem ms6_keep18 : rankKeep ms6 (3 / 7) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank18]
  decide +kernel
theorem ms6_rank19 : rank2 ms6 (4 / 9) = 80 := by kernel_rfl
theorem ms6_keep19 : rankKeep ms6 (4 / 9) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank19]
  decide +kernel
theorem ms6_rank20 : rank2 ms6 (1 / 2) = 93 := by kernel_rfl
theorem ms6_keep20 : rankKeep ms6 (1 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank20]
  decide +kernel
theorem ms6_rank21 : rank2 ms6 (4 / 7) = 107 := by kernel_rfl
theorem ms6_keep21 : rankKeep ms6 (4 / 7) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank21]
  decide +kernel
theorem ms6_rank22 : rank2 ms6 (3 / 5) = 111 := by kernel_rfl
theorem ms6_keep22 : rankKeep ms6 (3 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank22]
  decide +kernel
theorem ms6_rank23 : rank2 ms6 (2 / 3) = 124 := by kernel_rfl
theorem ms6_keep23 : rankKeep ms6 (2 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank23]
  decide +kernel
theorem ms6_rank24 : rank2 ms6 (8 / 11) = 137 := by kernel_rfl
theorem ms6_keep24 : rankKeep ms6 (8 / 11) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank24]
  decide +kernel
theorem ms6_rank25 : rank2 ms6 (3 / 4) = 141 := by kernel_rfl
theorem ms6_keep25 : rankKeep ms6 (3 / 4) 3 10 = true := by
  unfold rankKeep
  rw [ms6_length, ms6_rank25]
  decide +kernel
theorem ms6_rank26 : rank2 ms6 (7 / 9) = 146 := by kernel_rfl
theorem ms6_keep26 : rankKeep ms6 (7 / 9) 3 10 = true := by
  unfold rankKeep
  rw [ms6_length, ms6_rank26]
  decide +kernel
theorem ms6_rank27 : rank2 ms6 (14 / 17) = 150 := by kernel_rfl
theorem ms6_keep27 : rankKeep ms6 (14 / 17) 3 10 = true := by
  unfold rankKeep
  rw [ms6_length, ms6_rank27]
  decide +kernel
theorem ms6_rank28 : rank2 ms6 (6 / 7) = 152 := by kernel_rfl
theorem ms6_keep28 : rankKeep ms6 (6 / 7) 3 10 = true := by
  unfold rankKeep
  rw [ms6_length, ms6_rank28]
  decide +kernel
theorem ms6_rank29 : rank2 ms6 (8 / 9) = 154 := by kernel_rfl
theorem ms6_keep29 : rankKeep ms6 (8 / 9) 3 10 = true := by
  unfold rankKeep
  rw [ms6_length, ms6_rank29]
  decide +kernel
theorem ms6_rank30 : rank2 ms6 (15 / 16) = 156 := by kernel_rfl
theorem ms6_keep30 : rankKeep ms6 (15 / 16) 3 10 = true := by
  unfold rankKeep
  rw [ms6_length, ms6_rank30]
  decide +kernel
theorem ms6_rank31 : rank2 ms6 (1 / 1) = 207 := by kernel_rfl
theorem ms6_keep31 : rankKeep ms6 (1 / 1) 3 10 = true := by
  unfold rankKeep
  rw [ms6_length, ms6_rank31]
  decide +kernel
theorem ms6_rank32 : rank2 ms6 (6 / 5) = 258 := by kernel_rfl
theorem ms6_keep32 : rankKeep ms6 (6 / 5) 3 10 = true := by
  unfold rankKeep
  rw [ms6_length, ms6_rank32]
  decide +kernel
theorem ms6_rank33 : rank2 ms6 (5 / 4) = 261 := by kernel_rfl
theorem ms6_keep33 : rankKeep ms6 (5 / 4) 3 10 = true := by
  unfold rankKeep
  rw [ms6_length, ms6_rank33]
  decide +kernel
theorem ms6_rank34 : rank2 ms6 (4 / 3) = 266 := by kernel_rfl
theorem ms6_keep34 : rankKeep ms6 (4 / 3) 3 10 = true := by
  unfold rankKeep
  rw [ms6_length, ms6_rank34]
  decide +kernel
theorem ms6_rank35 : rank2 ms6 (11 / 8) = 270 := by kernel_rfl
theorem ms6_keep35 : rankKeep ms6 (11 / 8) 3 10 = true := by
  unfold rankKeep
  rw [ms6_length, ms6_rank35]
  decide +kernel
theorem ms6_rank36 : rank2 ms6 (7 / 5) = 272 := by kernel_rfl
theorem ms6_keep36 : rankKeep ms6 (7 / 5) 3 10 = true := by
  unfold rankKeep
  rw [ms6_length, ms6_rank36]
  decide +kernel
theorem ms6_rank37 : rank2 ms6 (13 / 9) = 274 := by kernel_rfl
theorem ms6_keep37 : rankKeep ms6 (13 / 9) 3 10 = true := by
  unfold rankKeep
  rw [ms6_length, ms6_rank37]
  decide +kernel
theorem ms6_rank38 : rank2 ms6 (3 / 2) = 283 := by kernel_rfl
theorem ms6_keep38 : rankKeep ms6 (3 / 2) 3 10 = true := by
  unfold rankKeep
  rw [ms6_length, ms6_rank38]
  decide +kernel
theorem ms6_rank39 : rank2 ms6 (8 / 5) = 292 := by kernel_rfl
theorem ms6_keep39 : rankKeep ms6 (8 / 5) 3 10 = true := by
  unfold rankKeep
  rw [ms6_length, ms6_rank39]
  decide +kernel
theorem ms6_rank40 : rank2 ms6 (5 / 3) = 298 := by kernel_rfl
theorem ms6_keep40 : rankKeep ms6 (5 / 3) 3 10 = true := by
  unfold rankKeep
  rw [ms6_length, ms6_rank40]
  decide +kernel
theorem ms6_rank41 : rank2 ms6 (7 / 4) = 305 := by kernel_rfl
theorem ms6_keep41 : rankKeep ms6 (7 / 4) 3 10 = true := by
  unfold rankKeep
  rw [ms6_length, ms6_rank41]
  decide +kernel
theorem ms6_rank42 : rank2 ms6 (2 / 1) = 330 := by kernel_rfl
theorem ms6_keep42 : rankKeep ms6 (2 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank42]
  decide +kernel
theorem ms6_rank43 : rank2 ms6 (37 / 16) = 354 := by kernel_rfl
theorem ms6_keep43 : rankKeep ms6 (37 / 16) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank43]
  decide +kernel
theorem ms6_rank44 : rank2 ms6 (7 / 3) = 358 := by kernel_rfl
theorem ms6_keep44 : rankKeep ms6 (7 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank44]
  decide +kernel
theorem ms6_rank45 : rank2 ms6 (12 / 5) = 362 := by kernel_rfl
theorem ms6_keep45 : rankKeep ms6 (12 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank45]
  decide +kernel
theorem ms6_rank46 : rank2 ms6 (17 / 7) = 364 := by kernel_rfl
theorem ms6_keep46 : rankKeep ms6 (17 / 7) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank46]
  decide +kernel
theorem ms6_rank47 : rank2 ms6 (5 / 2) = 366 := by kernel_rfl
theorem ms6_keep47 : rankKeep ms6 (5 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank47]
  decide +kernel
theorem ms6_rank48 : rank2 ms6 (8 / 3) = 368 := by kernel_rfl
theorem ms6_keep48 : rankKeep ms6 (8 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank48]
  decide +kernel
theorem ms6_rank49 : rank2 ms6 (23 / 8) = 370 := by kernel_rfl
theorem ms6_keep49 : rankKeep ms6 (23 / 8) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank49]
  decide +kernel
theorem ms6_rank50 : rank2 ms6 (3 / 1) = 386 := by kernel_rfl
theorem ms6_keep50 : rankKeep ms6 (3 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank50]
  decide +kernel
theorem ms6_rank51 : rank2 ms6 (10 / 3) = 403 := by kernel_rfl
theorem ms6_keep51 : rankKeep ms6 (10 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank51]
  decide +kernel
theorem ms6_rank52 : rank2 ms6 (4 / 1) = 412 := by kernel_rfl
theorem ms6_keep52 : rankKeep ms6 (4 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank52]
  decide +kernel
theorem ms6_rank53 : rank2 ms6 (13 / 3) = 420 := by kernel_rfl
theorem ms6_keep53 : rankKeep ms6 (13 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank53]
  decide +kernel
theorem ms6_rank54 : rank2 ms6 (9 / 2) = 422 := by kernel_rfl
theorem ms6_keep54 : rankKeep ms6 (9 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank54]
  decide +kernel
theorem ms6_rank55 : rank2 ms6 (5 / 1) = 425 := by kernel_rfl
theorem ms6_keep55 : rankKeep ms6 (5 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank55]
  decide +kernel
theorem ms6_rank56 : rank2 ms6 (11 / 2) = 429 := by kernel_rfl
theorem ms6_keep56 : rankKeep ms6 (11 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank56]
  decide +kernel
theorem ms6_rank57 : rank2 ms6 (6 / 1) = 432 := by kernel_rfl
theorem ms6_keep57 : rankKeep ms6 (6 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank57]
  decide +kernel
theorem ms6_rank58 : rank2 ms6 (13 / 2) = 434 := by kernel_rfl
theorem ms6_keep58 : rankKeep ms6 (13 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank58]
  decide +kernel
theorem ms6_rank59 : rank2 ms6 (7 / 1) = 437 := by kernel_rfl
theorem ms6_keep59 : rankKeep ms6 (7 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank59]
  decide +kernel
theorem ms6_rank60 : rank2 ms6 (8 / 1) = 443 := by kernel_rfl
theorem ms6_keep60 : rankKeep ms6 (8 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank60]
  decide +kernel
theorem ms6_rank61 : rank2 ms6 (9 / 1) = 449 := by kernel_rfl
theorem ms6_keep61 : rankKeep ms6 (9 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank61]
  decide +kernel
theorem ms6_rank62 : rank2 ms6 (11 / 1) = 453 := by kernel_rfl
theorem ms6_keep62 : rankKeep ms6 (11 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms6_length, ms6_rank62]
  decide +kernel
theorem aa6_length : aa6.length = 227 := by kernel_rfl
theorem aa6_rank0 : rank2 aa6 (1 / 1) = 27 := by kernel_rfl
theorem aa6_keep0 : rankKeep aa6 (1 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank0]
  decide +kernel
theorem aa6_rank1 : rank2 aa6 (2 / 1) = 77 := by kernel_rfl
theorem aa6_keep1 : rankKeep aa6 (2 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank1]
  decide +kernel
theorem aa6_rank2 : rank2 aa6 (3 / 1) = 115 := by kernel_rfl
theorem aa6_keep2 : rankKeep aa6 (3 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank2]
  decide +kernel
theorem aa6_rank3 : rank2 aa6 (4 / 1) = 150 := by kernel_rfl
theorem aa6_keep3 : rankKeep aa6 (4 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank3]
  decide +kernel
theorem aa6_rank4 : rank2 aa6 (5 / 1) = 173 := by kernel_rfl
theorem aa6_keep4 : rankKeep aa6 (5 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank4]
  decide +kernel
theorem aa6_rank5 : rank2 aa6 (6 / 1) = 191 := by kernel_rfl
theorem aa6_keep5 : rankKeep aa6 (6 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank5]
  decide +kernel
theorem aa6_rank6 : rank2 aa6 (7 / 1) = 208 := by kernel_rfl
theorem aa6_keep6 : rankKeep aa6 (7 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank6]
  decide +kernel
theorem aa6_rank7 : rank2 aa6 (8 / 1) = 221 := by kernel_rfl
theorem aa6_keep7 : rankKeep aa6 (8 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank7]
  decide +kernel
theorem aa6_rank8 : rank2 aa6 (9 / 1) = 239 := by kernel_rfl
theorem aa6_keep8 : rankKeep aa6 (9 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank8]
  decide +kernel
theorem aa6_rank9 : rank2 aa6 (10 / 1) = 255 := by kernel_rfl
theorem aa6_keep9 : rankKeep aa6 (10 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank9]
  decide +kernel
theorem aa6_rank10 : rank2 aa6 (11 / 1) = 268 := by kernel_rfl
theorem aa6_keep10 : rankKeep aa6 (11 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank10]
  decide +kernel
theorem aa6_rank11 : rank2 aa6 (12 / 1) = 281 := by kernel_rfl
theorem aa6_keep11 : rankKeep aa6 (12 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank11]
  decide +kernel
theorem aa6_rank12 : rank2 aa6 (15 / 1) = 297 := by kernel_rfl
theorem aa6_keep12 : rankKeep aa6 (15 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank12]
  decide +kernel
theorem aa6_rank13 : rank2 aa6 (16 / 1) = 309 := by kernel_rfl
theorem aa6_keep13 : rankKeep aa6 (16 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank13]
  decide +kernel
theorem aa6_rank14 : rank2 aa6 (18 / 1) = 320 := by kernel_rfl
theorem aa6_keep14 : rankKeep aa6 (18 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank14]
  decide +kernel
theorem aa6_rank15 : rank2 aa6 (20 / 1) = 326 := by kernel_rfl
theorem aa6_keep15 : rankKeep aa6 (20 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank15]
  decide +kernel
theorem aa6_rank16 : rank2 aa6 (21 / 1) = 330 := by kernel_rfl
theorem aa6_keep16 : rankKeep aa6 (21 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank16]
  decide +kernel
theorem aa6_rank17 : rank2 aa6 (22 / 1) = 336 := by kernel_rfl
theorem aa6_keep17 : rankKeep aa6 (22 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank17]
  decide +kernel
theorem aa6_rank18 : rank2 aa6 (24 / 1) = 342 := by kernel_rfl
theorem aa6_keep18 : rankKeep aa6 (24 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank18]
  decide +kernel
theorem aa6_rank19 : rank2 aa6 (25 / 1) = 348 := by kernel_rfl
theorem aa6_keep19 : rankKeep aa6 (25 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank19]
  decide +kernel
theorem aa6_rank20 : rank2 aa6 (26 / 1) = 352 := by kernel_rfl
theorem aa6_keep20 : rankKeep aa6 (26 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank20]
  decide +kernel
theorem aa6_rank21 : rank2 aa6 (27 / 1) = 357 := by kernel_rfl
theorem aa6_keep21 : rankKeep aa6 (27 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank21]
  decide +kernel
theorem aa6_rank22 : rank2 aa6 (28 / 1) = 366 := by kernel_rfl
theorem aa6_keep22 : rankKeep aa6 (28 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank22]
  decide +kernel
theorem aa6_rank23 : rank2 aa6 (30 / 1) = 374 := by kernel_rfl
theorem aa6_keep23 : rankKeep aa6 (30 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank23]
  decide +kernel
theorem aa6_rank24 : rank2 aa6 (35 / 1) = 378 := by kernel_rfl
theorem aa6_keep24 : rankKeep aa6 (35 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank24]
  decide +kernel
theorem aa6_rank25 : rank2 aa6 (36 / 1) = 382 := by kernel_rfl
theorem aa6_keep25 : rankKeep aa6 (36 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank25]
  decide +kernel
theorem aa6_rank26 : rank2 aa6 (39 / 1) = 387 := by kernel_rfl
theorem aa6_keep26 : rankKeep aa6 (39 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank26]
  decide +kernel
theorem aa6_rank27 : rank2 aa6 (40 / 1) = 390 := by kernel_rfl
theorem aa6_keep27 : rankKeep aa6 (40 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank27]
  decide +kernel
theorem aa6_rank28 : rank2 aa6 (42 / 1) = 392 := by kernel_rfl
theorem aa6_keep28 : rankKeep aa6 (42 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank28]
  decide +kernel
theorem aa6_rank29 : rank2 aa6 (49 / 1) = 394 := by kernel_rfl
theorem aa6_keep29 : rankKeep aa6 (49 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank29]
  decide +kernel
theorem aa6_rank30 : rank2 aa6 (50 / 1) = 397 := by kernel_rfl
theorem aa6_keep30 : rankKeep aa6 (50 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank30]
  decide +kernel
theorem aa6_rank31 : rank2 aa6 (54 / 1) = 402 := by kernel_rfl
theorem aa6_keep31 : rankKeep aa6 (54 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank31]
  decide +kernel
theorem aa6_rank32 : rank2 aa6 (60 / 1) = 406 := by kernel_rfl
theorem aa6_keep32 : rankKeep aa6 (60 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank32]
  decide +kernel
theorem aa6_rank33 : rank2 aa6 (63 / 1) = 410 := by kernel_rfl
theorem aa6_keep33 : rankKeep aa6 (63 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank33]
  decide +kernel
theorem aa6_rank34 : rank2 aa6 (64 / 1) = 414 := by kernel_rfl
theorem aa6_keep34 : rankKeep aa6 (64 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank34]
  decide +kernel
theorem aa6_rank35 : rank2 aa6 (69 / 1) = 416 := by kernel_rfl
theorem aa6_keep35 : rankKeep aa6 (69 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank35]
  decide +kernel
theorem aa6_rank36 : rank2 aa6 (72 / 1) = 418 := by kernel_rfl
theorem aa6_keep36 : rankKeep aa6 (72 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank36]
  decide +kernel
theorem aa6_rank37 : rank2 aa6 (80 / 1) = 421 := by kernel_rfl
theorem aa6_keep37 : rankKeep aa6 (80 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank37]
  decide +kernel
theorem aa6_rank38 : rank2 aa6 (84 / 1) = 424 := by kernel_rfl
theorem aa6_keep38 : rankKeep aa6 (84 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank38]
  decide +kernel
theorem aa6_rank39 : rank2 aa6 (88 / 1) = 427 := by kernel_rfl
theorem aa6_keep39 : rankKeep aa6 (88 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank39]
  decide +kernel
theorem aa6_rank40 : rank2 aa6 (95 / 1) = 430 := by kernel_rfl
theorem aa6_keep40 : rankKeep aa6 (95 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank40]
  decide +kernel
theorem aa6_rank41 : rank2 aa6 (100 / 1) = 432 := by kernel_rfl
theorem aa6_keep41 : rankKeep aa6 (100 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa6_length, aa6_rank41]
  decide +kernel
theorem aa6_rank42 : rank2 aa6 (104 / 1) = 434 := by kernel_rfl
theorem aa6_keep42 : rankKeep aa6 (104 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa6_length, aa6_rank42]
  decide +kernel
theorem aa6_rank43 : rank2 aa6 (117 / 1) = 436 := by kernel_rfl
theorem aa6_keep43 : rankKeep aa6 (117 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa6_length, aa6_rank43]
  decide +kernel
theorem aa6_rank44 : rank2 aa6 (119 / 1) = 438 := by kernel_rfl
theorem aa6_keep44 : rankKeep aa6 (119 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa6_length, aa6_rank44]
  decide +kernel
theorem aa6_rank45 : rank2 aa6 (174 / 1) = 440 := by kernel_rfl
theorem aa6_keep45 : rankKeep aa6 (174 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa6_length, aa6_rank45]
  decide +kernel
theorem aa6_rank46 : rank2 aa6 (184 / 1) = 442 := by kernel_rfl
theorem aa6_keep46 : rankKeep aa6 (184 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa6_length, aa6_rank46]
  decide +kernel
theorem aa6_rank47 : rank2 aa6 (192 / 1) = 444 := by kernel_rfl
theorem aa6_keep47 : rankKeep aa6 (192 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa6_length, aa6_rank47]
  decide +kernel
theorem aa6_rank48 : rank2 aa6 (238 / 1) = 446 := by kernel_rfl
theorem aa6_keep48 : rankKeep aa6 (238 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa6_length, aa6_rank48]
  decide +kernel
theorem aa6_rank49 : rank2 aa6 (240 / 1) = 449 := by kernel_rfl
theorem aa6_keep49 : rankKeep aa6 (240 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa6_length, aa6_rank49]
  decide +kernel
theorem aa6_rank50 : rank2 aa6 (352 / 1) = 452 := by kernel_rfl
theorem aa6_keep50 : rankKeep aa6 (352 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa6_length, aa6_rank50]
  decide +kernel
theorem aa6_rank51 : rank2 aa6 (592 / 1) = 454 := by kernel_rfl
theorem aa6_keep51 : rankKeep aa6 (592 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa6_length, aa6_rank51]
  decide +kernel
end Proofs.Witness
