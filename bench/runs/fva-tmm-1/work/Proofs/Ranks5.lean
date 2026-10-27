import Proofs.WitnessData
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Proofs.Witness
def ps5 : List (Nat × Nat) := [(3, 4), (9, 9), (2, 2), (1, 1), (1, 1), (3, 3), (2, 2), (5, 4), (2, 2), (2, 3), (2, 3), (5, 3), (5, 6), (9, 7), (8, 5), (2, 3), (1, 1), (6, 9), (5, 5), (3, 3), (1, 1), (2, 3), (3, 2), (3, 2), (2, 2), (1, 1), (2, 3), (1, 1), (1, 1), (1, 1), (4, 3), (11, 7), (3, 2), (1, 1), (3, 2), (1, 1), (6, 9), (7, 9), (1, 1), (2, 2), (1, 1), (4, 3), (1, 1), (3, 2), (8, 8), (7, 7), (6, 6), (2, 2), (1, 1), (2, 2), (3, 3), (6, 5), (4, 5), (1, 1), (1, 1), (7, 6), (9, 11), (2, 2), (3, 2), (1, 1), (1, 1), (1, 1), (2, 2), (1, 1), (5, 4), (2, 2), (4, 3), (1, 1), (6, 5), (2, 3), (1, 1), (3, 2), (2, 3), (4, 5), (4, 5), (5, 3), (2, 3), (9, 9), (2, 2), (3, 4), (1, 1), (1, 1), (2, 3), (2, 3), (1, 1), (2, 2), (2, 3), (1, 1), (5, 5), (11, 9), (1, 1), (5, 6), (1, 1), (1, 1), (3, 2)]
def allps5 : List (Nat × Nat) := [(3, 4), (1, 2), (4, 1), (1, 7), (11, 4), (15, 10), (9, 9), (1, 2), (1, 3), (2, 2), (1, 2), (9, 4), (1, 1), (1, 1), (3, 3), (10, 16), (2, 2), (5, 4), (2, 9), (3, 11), (8, 2), (1, 2), (2, 2), (2, 1), (4, 1), (2, 3), (2, 3), (5, 3), (5, 6), (5, 2), (9, 1), (8, 1), (2, 1), (12, 7), (3, 1), (9, 7), (8, 5), (2, 3), (1, 2), (1, 1), (6, 9), (3, 1), (5, 5), (18, 25), (3, 3), (4, 11), (3, 9), (12, 12), (6, 2), (1, 1), (2, 12), (2, 1), (4, 17), (12, 4), (2, 3), (1, 2), (1, 3), (3, 2), (2, 9), (3, 2), (4, 2), (1, 3), (8, 3), (7, 2), (2, 2), (1, 3), (1, 1), (7, 1), (12, 19), (3, 1), (2, 3), (1, 1), (10, 5), (1, 1), (2, 1), (5, 16), (3, 1), (1, 1), (9, 4), (4, 3), (11, 7), (10, 16), (1, 3), (3, 2), (13, 13), (1, 1), (1, 2), (3, 1), (9, 4), (3, 2), (2, 4), (1, 1), (5, 1), (1, 2), (6, 9), (9, 29), (7, 9), (4, 8), (13, 9), (3, 6), (6, 2), (1, 1), (1, 5), (8, 1), (2, 2), (1, 2), (1, 4), (1, 1), (1, 2), (4, 3), (7, 1), (4, 2), (2, 4), (4, 1), (11, 3), (14, 1), (2, 1), (2, 1), (2, 1), (1, 1), (3, 1), (3, 2), (2, 1), (8, 8), (7, 7), (6, 6), (7, 2), (2, 2), (1, 1), (2, 1), (2, 2), (3, 1), (3, 3), (6, 5), (4, 1), (3, 8), (4, 5), (3, 1), (1, 1), (8, 3), (1, 2), (5, 13), (5, 2), (9, 1), (1, 1), (7, 6), (9, 11), (3, 1), (1, 5), (2, 2), (3, 2), (4, 2), (1, 1), (6, 1), (1, 2), (1, 1), (4, 1), (1, 2), (2, 1), (5, 23), (1, 1), (2, 2), (4, 1), (1, 1), (5, 4), (3, 5), (2, 2), (4, 2), (4, 3), (1, 1), (1, 2), (10, 4), (2, 6), (2, 1), (2, 4), (2, 1), (6, 5), (2, 3), (1, 4), (16, 10), (1, 1), (1, 3), (10, 3), (3, 2), (2, 3), (2, 9), (4, 5), (3, 7), (11, 2), (5, 8), (4, 5), (5, 3), (2, 3), (9, 9), (2, 2), (3, 4), (1, 1), (6, 2), (3, 1), (2, 6), (2, 4), (1, 2), (1, 1), (1, 11), (13, 2), (3, 1), (2, 4), (2, 3), (2, 3), (1, 1), (2, 9), (2, 2), (6, 2), (2, 3), (1, 2), (1, 10), (1, 5), (1, 1), (5, 5), (15, 11), (13, 10), (11, 9), (1, 2), (1, 1), (1, 2), (11, 3), (1, 2), (1, 5), (1, 2), (3, 1), (1, 4), (5, 6), (1, 1), (16, 7), (1, 1), (14, 6), (1, 2), (3, 2), (3, 1), (3, 1), (5, 10), (3, 9), (5, 2), (2, 1)]
def ms5 : List ℚ := [(3 / 4), (1 / 2), (4 / 1), (1 / 7), (11 / 4), (3 / 2), (1 / 1), (1 / 2), (1 / 3), (1 / 1), (1 / 2), (9 / 4), (1 / 1), (1 / 1), (1 / 1), (5 / 8), (1 / 1), (5 / 4), (2 / 9), (3 / 11), (4 / 1), (1 / 2), (1 / 1), (2 / 1), (4 / 1), (2 / 3), (2 / 3), (5 / 3), (5 / 6), (5 / 2), (9 / 1), (8 / 1), (2 / 1), (12 / 7), (3 / 1), (9 / 7), (8 / 5), (2 / 3), (1 / 2), (1 / 1), (2 / 3), (3 / 1), (1 / 1), (18 / 25), (1 / 1), (4 / 11), (1 / 3), (1 / 1), (3 / 1), (1 / 1), (1 / 6), (2 / 1), (4 / 17), (3 / 1), (2 / 3), (1 / 2), (1 / 3), (3 / 2), (2 / 9), (3 / 2), (2 / 1), (1 / 3), (8 / 3), (7 / 2), (1 / 1), (1 / 3), (1 / 1), (7 / 1), (12 / 19), (3 / 1), (2 / 3), (1 / 1), (2 / 1), (1 / 1), (2 / 1), (5 / 16), (3 / 1), (1 / 1), (9 / 4), (4 / 3), (11 / 7), (5 / 8), (1 / 3), (3 / 2), (1 / 1), (1 / 1), (1 / 2), (3 / 1), (9 / 4), (3 / 2), (1 / 2), (1 / 1), (5 / 1), (1 / 2), (2 / 3), (9 / 29), (7 / 9), (1 / 2), (13 / 9), (1 / 2), (3 / 1), (1 / 1), (1 / 5), (8 / 1), (1 / 1), (1 / 2), (1 / 4), (1 / 1), (1 / 2), (4 / 3), (7 / 1), (2 / 1), (1 / 2), (4 / 1), (11 / 3), (14 / 1), (2 / 1), (2 / 1), (2 / 1), (1 / 1), (3 / 1), (3 / 2), (2 / 1), (1 / 1), (1 / 1), (1 / 1), (7 / 2), (1 / 1), (1 / 1), (2 / 1), (1 / 1), (3 / 1), (1 / 1), (6 / 5), (4 / 1), (3 / 8), (4 / 5), (3 / 1), (1 / 1), (8 / 3), (1 / 2), (5 / 13), (5 / 2), (9 / 1), (1 / 1), (7 / 6), (9 / 11), (3 / 1), (1 / 5), (1 / 1), (3 / 2), (2 / 1), (1 / 1), (6 / 1), (1 / 2), (1 / 1), (4 / 1), (1 / 2), (2 / 1), (5 / 23), (1 / 1), (1 / 1), (4 / 1), (1 / 1), (5 / 4), (3 / 5), (1 / 1), (2 / 1), (4 / 3), (1 / 1), (1 / 2), (5 / 2), (1 / 3), (2 / 1), (1 / 2), (2 / 1), (6 / 5), (2 / 3), (1 / 4), (8 / 5), (1 / 1), (1 / 3), (10 / 3), (3 / 2), (2 / 3), (2 / 9), (4 / 5), (3 / 7), (11 / 2), (5 / 8), (4 / 5), (5 / 3), (2 / 3), (1 / 1), (1 / 1), (3 / 4), (1 / 1), (3 / 1), (3 / 1), (1 / 3), (1 / 2), (1 / 2), (1 / 1), (1 / 11), (13 / 2), (3 / 1), (1 / 2), (2 / 3), (2 / 3), (1 / 1), (2 / 9), (1 / 1), (3 / 1), (2 / 3), (1 / 2), (1 / 10), (1 / 5), (1 / 1), (1 / 1), (15 / 11), (13 / 10), (11 / 9), (1 / 2), (1 / 1), (1 / 2), (11 / 3), (1 / 2), (1 / 5), (1 / 2), (3 / 1), (1 / 4), (5 / 6), (1 / 1), (16 / 7), (1 / 1), (7 / 3), (1 / 2), (3 / 2), (3 / 1), (3 / 1), (1 / 2), (1 / 3), (5 / 2), (2 / 1)]
def aa5 : List ℚ := [12, 2, 4, 7, 44, 150, 81, 2, 3, 4, 2, 36, 1, 1, 9, 160, 4, 20, 18, 33, 16, 2, 4, 2, 4, 6, 6, 15, 30, 10, 9, 8, 2, 84, 3, 63, 40, 6, 2, 1, 54, 3, 25, 450, 9, 44, 27, 144, 12, 1, 24, 2, 68, 48, 6, 2, 3, 6, 18, 6, 8, 3, 24, 14, 4, 3, 1, 7, 228, 3, 6, 1, 50, 1, 2, 80, 3, 1, 36, 12, 77, 160, 3, 6, 169, 1, 2, 3, 36, 6, 8, 1, 5, 2, 54, 261, 63, 32, 117, 18, 12, 1, 5, 8, 4, 2, 4, 1, 2, 12, 7, 8, 8, 4, 33, 14, 2, 2, 2, 1, 3, 6, 2, 64, 49, 36, 14, 4, 1, 2, 4, 3, 9, 30, 4, 24, 20, 3, 1, 24, 2, 65, 10, 9, 1, 42, 99, 3, 5, 4, 6, 8, 1, 6, 2, 1, 4, 2, 2, 115, 1, 4, 4, 1, 20, 15, 4, 8, 12, 1, 2, 40, 12, 2, 8, 2, 30, 6, 4, 160, 1, 3, 30, 6, 6, 18, 20, 21, 22, 40, 20, 15, 6, 81, 4, 12, 1, 12, 3, 12, 8, 2, 1, 11, 26, 3, 8, 6, 6, 1, 18, 4, 12, 6, 2, 10, 5, 1, 25, 165, 130, 99, 2, 1, 2, 33, 2, 5, 2, 3, 4, 30, 1, 112, 1, 84, 2, 6, 3, 3, 50, 27, 10, 2]
theorem pairs5 : pairs matrix 5 3 = allps5 := by kernel_rfl
theorem ms_eq5 : allps5.map (fun p => (p.1 : ℚ) / p.2) = ms5 := by kernel_rfl
theorem aa_eq5 : allps5.map (fun p => ((p.1 * p.2 : Nat) : ℚ)) = aa5 := by kernel_rfl
theorem ms5_length : ms5.length = 244 := by kernel_rfl
theorem ms5_rank0 : rank2 ms5 (1 / 11) = 2 := by kernel_rfl
theorem ms5_keep0 : rankKeep ms5 (1 / 11) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank0]
  decide +kernel
theorem ms5_rank1 : rank2 ms5 (1 / 10) = 4 := by kernel_rfl
theorem ms5_keep1 : rankKeep ms5 (1 / 10) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank1]
  decide +kernel
theorem ms5_rank2 : rank2 ms5 (1 / 7) = 6 := by kernel_rfl
theorem ms5_keep2 : rankKeep ms5 (1 / 7) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank2]
  decide +kernel
theorem ms5_rank3 : rank2 ms5 (1 / 6) = 8 := by kernel_rfl
theorem ms5_keep3 : rankKeep ms5 (1 / 6) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank3]
  decide +kernel
theorem ms5_rank4 : rank2 ms5 (1 / 5) = 13 := by kernel_rfl
theorem ms5_keep4 : rankKeep ms5 (1 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank4]
  decide +kernel
theorem ms5_rank5 : rank2 ms5 (5 / 23) = 18 := by kernel_rfl
theorem ms5_keep5 : rankKeep ms5 (5 / 23) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank5]
  decide +kernel
theorem ms5_rank6 : rank2 ms5 (2 / 9) = 23 := by kernel_rfl
theorem ms5_keep6 : rankKeep ms5 (2 / 9) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank6]
  decide +kernel
theorem ms5_rank7 : rank2 ms5 (4 / 17) = 28 := by kernel_rfl
theorem ms5_keep7 : rankKeep ms5 (4 / 17) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank7]
  decide +kernel
theorem ms5_rank8 : rank2 ms5 (1 / 4) = 32 := by kernel_rfl
theorem ms5_keep8 : rankKeep ms5 (1 / 4) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank8]
  decide +kernel
theorem ms5_rank9 : rank2 ms5 (3 / 11) = 36 := by kernel_rfl
theorem ms5_keep9 : rankKeep ms5 (3 / 11) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank9]
  decide +kernel
theorem ms5_rank10 : rank2 ms5 (9 / 29) = 38 := by kernel_rfl
theorem ms5_keep10 : rankKeep ms5 (9 / 29) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank10]
  decide +kernel
theorem ms5_rank11 : rank2 ms5 (5 / 16) = 40 := by kernel_rfl
theorem ms5_keep11 : rankKeep ms5 (5 / 16) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank11]
  decide +kernel
theorem ms5_rank12 : rank2 ms5 (1 / 3) = 51 := by kernel_rfl
theorem ms5_keep12 : rankKeep ms5 (1 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank12]
  decide +kernel
theorem ms5_rank13 : rank2 ms5 (4 / 11) = 62 := by kernel_rfl
theorem ms5_keep13 : rankKeep ms5 (4 / 11) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank13]
  decide +kernel
theorem ms5_rank14 : rank2 ms5 (3 / 8) = 64 := by kernel_rfl
theorem ms5_keep14 : rankKeep ms5 (3 / 8) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank14]
  decide +kernel
theorem ms5_rank15 : rank2 ms5 (5 / 13) = 66 := by kernel_rfl
theorem ms5_keep15 : rankKeep ms5 (5 / 13) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank15]
  decide +kernel
theorem ms5_rank16 : rank2 ms5 (3 / 7) = 68 := by kernel_rfl
theorem ms5_keep16 : rankKeep ms5 (3 / 7) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank16]
  decide +kernel
theorem ms5_rank17 : rank2 ms5 (1 / 2) = 98 := by kernel_rfl
theorem ms5_keep17 : rankKeep ms5 (1 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank17]
  decide +kernel
theorem ms5_rank18 : rank2 ms5 (3 / 5) = 128 := by kernel_rfl
theorem ms5_keep18 : rankKeep ms5 (3 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank18]
  decide +kernel
theorem ms5_rank19 : rank2 ms5 (5 / 8) = 132 := by kernel_rfl
theorem ms5_keep19 : rankKeep ms5 (5 / 8) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank19]
  decide +kernel
theorem ms5_rank20 : rank2 ms5 (12 / 19) = 136 := by kernel_rfl
theorem ms5_keep20 : rankKeep ms5 (12 / 19) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank20]
  decide +kernel
theorem ms5_rank21 : rank2 ms5 (2 / 3) = 150 := by kernel_rfl
theorem ms5_keep21 : rankKeep ms5 (2 / 3) 3 10 = true := by
  unfold rankKeep
  rw [ms5_length, ms5_rank21]
  decide +kernel
theorem ms5_rank22 : rank2 ms5 (18 / 25) = 164 := by kernel_rfl
theorem ms5_keep22 : rankKeep ms5 (18 / 25) 3 10 = true := by
  unfold rankKeep
  rw [ms5_length, ms5_rank22]
  decide +kernel
theorem ms5_rank23 : rank2 ms5 (3 / 4) = 167 := by kernel_rfl
theorem ms5_keep23 : rankKeep ms5 (3 / 4) 3 10 = true := by
  unfold rankKeep
  rw [ms5_length, ms5_rank23]
  decide +kernel
theorem ms5_rank24 : rank2 ms5 (7 / 9) = 170 := by kernel_rfl
theorem ms5_keep24 : rankKeep ms5 (7 / 9) 3 10 = true := by
  unfold rankKeep
  rw [ms5_length, ms5_rank24]
  decide +kernel
theorem ms5_rank25 : rank2 ms5 (4 / 5) = 174 := by kernel_rfl
theorem ms5_keep25 : rankKeep ms5 (4 / 5) 3 10 = true := by
  unfold rankKeep
  rw [ms5_length, ms5_rank25]
  decide +kernel
theorem ms5_rank26 : rank2 ms5 (9 / 11) = 178 := by kernel_rfl
theorem ms5_keep26 : rankKeep ms5 (9 / 11) 3 10 = true := by
  unfold rankKeep
  rw [ms5_length, ms5_rank26]
  decide +kernel
theorem ms5_rank27 : rank2 ms5 (5 / 6) = 181 := by kernel_rfl
theorem ms5_keep27 : rankKeep ms5 (5 / 6) 3 10 = true := by
  unfold rankKeep
  rw [ms5_length, ms5_rank27]
  decide +kernel
theorem ms5_rank28 : rank2 ms5 (1 / 1) = 236 := by kernel_rfl
theorem ms5_keep28 : rankKeep ms5 (1 / 1) 3 10 = true := by
  unfold rankKeep
  rw [ms5_length, ms5_rank28]
  decide +kernel
theorem ms5_rank29 : rank2 ms5 (7 / 6) = 290 := by kernel_rfl
theorem ms5_keep29 : rankKeep ms5 (7 / 6) 3 10 = true := by
  unfold rankKeep
  rw [ms5_length, ms5_rank29]
  decide +kernel
theorem ms5_rank30 : rank2 ms5 (6 / 5) = 293 := by kernel_rfl
theorem ms5_keep30 : rankKeep ms5 (6 / 5) 3 10 = true := by
  unfold rankKeep
  rw [ms5_length, ms5_rank30]
  decide +kernel
theorem ms5_rank31 : rank2 ms5 (11 / 9) = 296 := by kernel_rfl
theorem ms5_keep31 : rankKeep ms5 (11 / 9) 3 10 = true := by
  unfold rankKeep
  rw [ms5_length, ms5_rank31]
  decide +kernel
theorem ms5_rank32 : rank2 ms5 (5 / 4) = 299 := by kernel_rfl
theorem ms5_keep32 : rankKeep ms5 (5 / 4) 3 10 = true := by
  unfold rankKeep
  rw [ms5_length, ms5_rank32]
  decide +kernel
theorem ms5_rank33 : rank2 ms5 (9 / 7) = 302 := by kernel_rfl
theorem ms5_keep33 : rankKeep ms5 (9 / 7) 3 10 = true := by
  unfold rankKeep
  rw [ms5_length, ms5_rank33]
  decide +kernel
theorem ms5_rank34 : rank2 ms5 (13 / 10) = 304 := by kernel_rfl
theorem ms5_keep34 : rankKeep ms5 (13 / 10) 3 10 = true := by
  unfold rankKeep
  rw [ms5_length, ms5_rank34]
  decide +kernel
theorem ms5_rank35 : rank2 ms5 (4 / 3) = 308 := by kernel_rfl
theorem ms5_keep35 : rankKeep ms5 (4 / 3) 3 10 = true := by
  unfold rankKeep
  rw [ms5_length, ms5_rank35]
  decide +kernel
theorem ms5_rank36 : rank2 ms5 (15 / 11) = 312 := by kernel_rfl
theorem ms5_keep36 : rankKeep ms5 (15 / 11) 3 10 = true := by
  unfold rankKeep
  rw [ms5_length, ms5_rank36]
  decide +kernel
theorem ms5_rank37 : rank2 ms5 (13 / 9) = 314 := by kernel_rfl
theorem ms5_keep37 : rankKeep ms5 (13 / 9) 3 10 = true := by
  unfold rankKeep
  rw [ms5_length, ms5_rank37]
  decide +kernel
theorem ms5_rank38 : rank2 ms5 (3 / 2) = 324 := by kernel_rfl
theorem ms5_keep38 : rankKeep ms5 (3 / 2) 3 10 = true := by
  unfold rankKeep
  rw [ms5_length, ms5_rank38]
  decide +kernel
theorem ms5_rank39 : rank2 ms5 (11 / 7) = 334 := by kernel_rfl
theorem ms5_keep39 : rankKeep ms5 (11 / 7) 3 10 = true := by
  unfold rankKeep
  rw [ms5_length, ms5_rank39]
  decide +kernel
theorem ms5_rank40 : rank2 ms5 (8 / 5) = 337 := by kernel_rfl
theorem ms5_keep40 : rankKeep ms5 (8 / 5) 3 10 = true := by
  unfold rankKeep
  rw [ms5_length, ms5_rank40]
  decide +kernel
theorem ms5_rank41 : rank2 ms5 (5 / 3) = 341 := by kernel_rfl
theorem ms5_keep41 : rankKeep ms5 (5 / 3) 3 10 = true := by
  unfold rankKeep
  rw [ms5_length, ms5_rank41]
  decide +kernel
theorem ms5_rank42 : rank2 ms5 (12 / 7) = 344 := by kernel_rfl
theorem ms5_keep42 : rankKeep ms5 (12 / 7) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank42]
  decide +kernel
theorem ms5_rank43 : rank2 ms5 (2 / 1) = 363 := by kernel_rfl
theorem ms5_keep43 : rankKeep ms5 (2 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank43]
  decide +kernel
theorem ms5_rank44 : rank2 ms5 (9 / 4) = 384 := by kernel_rfl
theorem ms5_keep44 : rankKeep ms5 (9 / 4) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank44]
  decide +kernel
theorem ms5_rank45 : rank2 ms5 (16 / 7) = 388 := by kernel_rfl
theorem ms5_keep45 : rankKeep ms5 (16 / 7) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank45]
  decide +kernel
theorem ms5_rank46 : rank2 ms5 (7 / 3) = 390 := by kernel_rfl
theorem ms5_keep46 : rankKeep ms5 (7 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank46]
  decide +kernel
theorem ms5_rank47 : rank2 ms5 (5 / 2) = 395 := by kernel_rfl
theorem ms5_keep47 : rankKeep ms5 (5 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank47]
  decide +kernel
theorem ms5_rank48 : rank2 ms5 (8 / 3) = 401 := by kernel_rfl
theorem ms5_keep48 : rankKeep ms5 (8 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank48]
  decide +kernel
theorem ms5_rank49 : rank2 ms5 (11 / 4) = 404 := by kernel_rfl
theorem ms5_keep49 : rankKeep ms5 (11 / 4) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank49]
  decide +kernel
theorem ms5_rank50 : rank2 ms5 (3 / 1) = 424 := by kernel_rfl
theorem ms5_keep50 : rankKeep ms5 (3 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank50]
  decide +kernel
theorem ms5_rank51 : rank2 ms5 (10 / 3) = 444 := by kernel_rfl
theorem ms5_keep51 : rankKeep ms5 (10 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank51]
  decide +kernel
theorem ms5_rank52 : rank2 ms5 (7 / 2) = 447 := by kernel_rfl
theorem ms5_keep52 : rankKeep ms5 (7 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank52]
  decide +kernel
theorem ms5_rank53 : rank2 ms5 (11 / 3) = 451 := by kernel_rfl
theorem ms5_keep53 : rankKeep ms5 (11 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank53]
  decide +kernel
theorem ms5_rank54 : rank2 ms5 (4 / 1) = 460 := by kernel_rfl
theorem ms5_keep54 : rankKeep ms5 (4 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank54]
  decide +kernel
theorem ms5_rank55 : rank2 ms5 (5 / 1) = 468 := by kernel_rfl
theorem ms5_keep55 : rankKeep ms5 (5 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank55]
  decide +kernel
theorem ms5_rank56 : rank2 ms5 (11 / 2) = 470 := by kernel_rfl
theorem ms5_keep56 : rankKeep ms5 (11 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank56]
  decide +kernel
theorem ms5_rank57 : rank2 ms5 (6 / 1) = 472 := by kernel_rfl
theorem ms5_keep57 : rankKeep ms5 (6 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank57]
  decide +kernel
theorem ms5_rank58 : rank2 ms5 (13 / 2) = 474 := by kernel_rfl
theorem ms5_keep58 : rankKeep ms5 (13 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank58]
  decide +kernel
theorem ms5_rank59 : rank2 ms5 (7 / 1) = 477 := by kernel_rfl
theorem ms5_keep59 : rankKeep ms5 (7 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank59]
  decide +kernel
theorem ms5_rank60 : rank2 ms5 (8 / 1) = 481 := by kernel_rfl
theorem ms5_keep60 : rankKeep ms5 (8 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank60]
  decide +kernel
theorem ms5_rank61 : rank2 ms5 (9 / 1) = 485 := by kernel_rfl
theorem ms5_keep61 : rankKeep ms5 (9 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank61]
  decide +kernel
theorem ms5_rank62 : rank2 ms5 (14 / 1) = 488 := by kernel_rfl
theorem ms5_keep62 : rankKeep ms5 (14 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms5_length, ms5_rank62]
  decide +kernel
theorem aa5_length : aa5.length = 244 := by kernel_rfl
theorem aa5_rank0 : rank2 aa5 (1 / 1) = 30 := by kernel_rfl
theorem aa5_keep0 : rankKeep aa5 (1 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank0]
  decide +kernel
theorem aa5_rank1 : rank2 aa5 (2 / 1) = 93 := by kernel_rfl
theorem aa5_keep1 : rankKeep aa5 (2 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank1]
  decide +kernel
theorem aa5_rank2 : rank2 aa5 (3 / 1) = 147 := by kernel_rfl
theorem aa5_keep2 : rankKeep aa5 (3 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank2]
  decide +kernel
theorem aa5_rank3 : rank2 aa5 (4 / 1) = 188 := by kernel_rfl
theorem aa5_keep3 : rankKeep aa5 (4 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank3]
  decide +kernel
theorem aa5_rank4 : rank2 aa5 (5 / 1) = 214 := by kernel_rfl
theorem aa5_keep4 : rankKeep aa5 (5 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank4]
  decide +kernel
theorem aa5_rank5 : rank2 aa5 (6 / 1) = 239 := by kernel_rfl
theorem aa5_keep5 : rankKeep aa5 (6 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank5]
  decide +kernel
theorem aa5_rank6 : rank2 aa5 (7 / 1) = 262 := by kernel_rfl
theorem aa5_keep6 : rankKeep aa5 (7 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank6]
  decide +kernel
theorem aa5_rank7 : rank2 aa5 (8 / 1) = 276 := by kernel_rfl
theorem aa5_keep7 : rankKeep aa5 (8 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank7]
  decide +kernel
theorem aa5_rank8 : rank2 aa5 (9 / 1) = 292 := by kernel_rfl
theorem aa5_keep8 : rankKeep aa5 (9 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank8]
  decide +kernel
theorem aa5_rank9 : rank2 aa5 (10 / 1) = 301 := by kernel_rfl
theorem aa5_keep9 : rankKeep aa5 (10 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank9]
  decide +kernel
theorem aa5_rank10 : rank2 aa5 (11 / 1) = 306 := by kernel_rfl
theorem aa5_keep10 : rankKeep aa5 (11 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank10]
  decide +kernel
theorem aa5_rank11 : rank2 aa5 (12 / 1) = 318 := by kernel_rfl
theorem aa5_keep11 : rankKeep aa5 (12 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank11]
  decide +kernel
theorem aa5_rank12 : rank2 aa5 (14 / 1) = 332 := by kernel_rfl
theorem aa5_keep12 : rankKeep aa5 (14 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank12]
  decide +kernel
theorem aa5_rank13 : rank2 aa5 (15 / 1) = 338 := by kernel_rfl
theorem aa5_keep13 : rankKeep aa5 (15 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank13]
  decide +kernel
theorem aa5_rank14 : rank2 aa5 (16 / 1) = 342 := by kernel_rfl
theorem aa5_keep14 : rankKeep aa5 (16 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank14]
  decide +kernel
theorem aa5_rank15 : rank2 aa5 (18 / 1) = 348 := by kernel_rfl
theorem aa5_keep15 : rankKeep aa5 (18 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank15]
  decide +kernel
theorem aa5_rank16 : rank2 aa5 (20 / 1) = 358 := by kernel_rfl
theorem aa5_keep16 : rankKeep aa5 (20 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank16]
  decide +kernel
theorem aa5_rank17 : rank2 aa5 (21 / 1) = 364 := by kernel_rfl
theorem aa5_keep17 : rankKeep aa5 (21 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank17]
  decide +kernel
theorem aa5_rank18 : rank2 aa5 (22 / 1) = 366 := by kernel_rfl
theorem aa5_keep18 : rankKeep aa5 (22 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank18]
  decide +kernel
theorem aa5_rank19 : rank2 aa5 (24 / 1) = 371 := by kernel_rfl
theorem aa5_keep19 : rankKeep aa5 (24 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank19]
  decide +kernel
theorem aa5_rank20 : rank2 aa5 (25 / 1) = 377 := by kernel_rfl
theorem aa5_keep20 : rankKeep aa5 (25 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank20]
  decide +kernel
theorem aa5_rank21 : rank2 aa5 (26 / 1) = 380 := by kernel_rfl
theorem aa5_keep21 : rankKeep aa5 (26 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank21]
  decide +kernel
theorem aa5_rank22 : rank2 aa5 (27 / 1) = 383 := by kernel_rfl
theorem aa5_keep22 : rankKeep aa5 (27 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank22]
  decide +kernel
theorem aa5_rank23 : rank2 aa5 (30 / 1) = 390 := by kernel_rfl
theorem aa5_keep23 : rankKeep aa5 (30 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank23]
  decide +kernel
theorem aa5_rank24 : rank2 aa5 (32 / 1) = 396 := by kernel_rfl
theorem aa5_keep24 : rankKeep aa5 (32 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank24]
  decide +kernel
theorem aa5_rank25 : rank2 aa5 (33 / 1) = 400 := by kernel_rfl
theorem aa5_keep25 : rankKeep aa5 (33 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank25]
  decide +kernel
theorem aa5_rank26 : rank2 aa5 (36 / 1) = 407 := by kernel_rfl
theorem aa5_keep26 : rankKeep aa5 (36 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank26]
  decide +kernel
theorem aa5_rank27 : rank2 aa5 (40 / 1) = 414 := by kernel_rfl
theorem aa5_keep27 : rankKeep aa5 (40 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank27]
  decide +kernel
theorem aa5_rank28 : rank2 aa5 (42 / 1) = 418 := by kernel_rfl
theorem aa5_keep28 : rankKeep aa5 (42 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank28]
  decide +kernel
theorem aa5_rank29 : rank2 aa5 (44 / 1) = 421 := by kernel_rfl
theorem aa5_keep29 : rankKeep aa5 (44 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank29]
  decide +kernel
theorem aa5_rank30 : rank2 aa5 (48 / 1) = 424 := by kernel_rfl
theorem aa5_keep30 : rankKeep aa5 (48 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank30]
  decide +kernel
theorem aa5_rank31 : rank2 aa5 (49 / 1) = 426 := by kernel_rfl
theorem aa5_keep31 : rankKeep aa5 (49 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank31]
  decide +kernel
theorem aa5_rank32 : rank2 aa5 (50 / 1) = 429 := by kernel_rfl
theorem aa5_keep32 : rankKeep aa5 (50 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank32]
  decide +kernel
theorem aa5_rank33 : rank2 aa5 (54 / 1) = 433 := by kernel_rfl
theorem aa5_keep33 : rankKeep aa5 (54 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank33]
  decide +kernel
theorem aa5_rank34 : rank2 aa5 (63 / 1) = 437 := by kernel_rfl
theorem aa5_keep34 : rankKeep aa5 (63 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank34]
  decide +kernel
theorem aa5_rank35 : rank2 aa5 (64 / 1) = 440 := by kernel_rfl
theorem aa5_keep35 : rankKeep aa5 (64 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank35]
  decide +kernel
theorem aa5_rank36 : rank2 aa5 (65 / 1) = 442 := by kernel_rfl
theorem aa5_keep36 : rankKeep aa5 (65 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank36]
  decide +kernel
theorem aa5_rank37 : rank2 aa5 (68 / 1) = 444 := by kernel_rfl
theorem aa5_keep37 : rankKeep aa5 (68 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank37]
  decide +kernel
theorem aa5_rank38 : rank2 aa5 (77 / 1) = 446 := by kernel_rfl
theorem aa5_keep38 : rankKeep aa5 (77 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank38]
  decide +kernel
theorem aa5_rank39 : rank2 aa5 (80 / 1) = 448 := by kernel_rfl
theorem aa5_keep39 : rankKeep aa5 (80 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank39]
  decide +kernel
theorem aa5_rank40 : rank2 aa5 (81 / 1) = 451 := by kernel_rfl
theorem aa5_keep40 : rankKeep aa5 (81 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank40]
  decide +kernel
theorem aa5_rank41 : rank2 aa5 (84 / 1) = 455 := by kernel_rfl
theorem aa5_keep41 : rankKeep aa5 (84 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank41]
  decide +kernel
theorem aa5_rank42 : rank2 aa5 (99 / 1) = 459 := by kernel_rfl
theorem aa5_keep42 : rankKeep aa5 (99 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank42]
  decide +kernel
theorem aa5_rank43 : rank2 aa5 (112 / 1) = 462 := by kernel_rfl
theorem aa5_keep43 : rankKeep aa5 (112 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank43]
  decide +kernel
theorem aa5_rank44 : rank2 aa5 (115 / 1) = 464 := by kernel_rfl
theorem aa5_keep44 : rankKeep aa5 (115 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa5_length, aa5_rank44]
  decide +kernel
theorem aa5_rank45 : rank2 aa5 (117 / 1) = 466 := by kernel_rfl
theorem aa5_keep45 : rankKeep aa5 (117 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa5_length, aa5_rank45]
  decide +kernel
theorem aa5_rank46 : rank2 aa5 (130 / 1) = 468 := by kernel_rfl
theorem aa5_keep46 : rankKeep aa5 (130 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa5_length, aa5_rank46]
  decide +kernel
theorem aa5_rank47 : rank2 aa5 (144 / 1) = 470 := by kernel_rfl
theorem aa5_keep47 : rankKeep aa5 (144 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa5_length, aa5_rank47]
  decide +kernel
theorem aa5_rank48 : rank2 aa5 (150 / 1) = 472 := by kernel_rfl
theorem aa5_keep48 : rankKeep aa5 (150 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa5_length, aa5_rank48]
  decide +kernel
theorem aa5_rank49 : rank2 aa5 (160 / 1) = 476 := by kernel_rfl
theorem aa5_keep49 : rankKeep aa5 (160 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa5_length, aa5_rank49]
  decide +kernel
theorem aa5_rank50 : rank2 aa5 (165 / 1) = 480 := by kernel_rfl
theorem aa5_keep50 : rankKeep aa5 (165 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa5_length, aa5_rank50]
  decide +kernel
theorem aa5_rank51 : rank2 aa5 (169 / 1) = 482 := by kernel_rfl
theorem aa5_keep51 : rankKeep aa5 (169 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa5_length, aa5_rank51]
  decide +kernel
theorem aa5_rank52 : rank2 aa5 (228 / 1) = 484 := by kernel_rfl
theorem aa5_keep52 : rankKeep aa5 (228 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa5_length, aa5_rank52]
  decide +kernel
theorem aa5_rank53 : rank2 aa5 (261 / 1) = 486 := by kernel_rfl
theorem aa5_keep53 : rankKeep aa5 (261 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa5_length, aa5_rank53]
  decide +kernel
theorem aa5_rank54 : rank2 aa5 (450 / 1) = 488 := by kernel_rfl
theorem aa5_keep54 : rankKeep aa5 (450 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa5_length, aa5_rank54]
  decide +kernel
end Proofs.Witness
