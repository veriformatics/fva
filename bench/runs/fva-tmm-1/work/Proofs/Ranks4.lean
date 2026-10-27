import Proofs.WitnessData
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Proofs.Witness
def ps4 : List (Nat × Nat) := [(2, 2), (4, 2), (4, 2), (6, 4), (4, 3), (9, 4), (17, 11), (6, 3), (2, 2), (2, 1), (2, 1), (13, 7), (2, 2), (7, 3), (4, 2), (9, 9), (5, 3), (7, 3), (15, 12), (2, 2), (6, 3), (2, 1), (4, 4), (3, 3), (5, 3), (2, 2), (2, 2), (3, 2), (4, 2), (15, 9), (17, 9), (3, 2), (3, 2), (3, 2), (5, 3), (7, 4), (2, 1), (2, 1), (7, 7), (2, 1), (2, 1), (11, 5), (2, 1), (5, 5), (2, 1), (3, 2), (2, 1), (6, 6), (16, 11), (2, 1), (3, 2), (2, 2), (2, 1), (3, 2), (4, 4), (5, 5), (5, 3), (2, 2), (2, 1), (6, 5), (11, 10), (3, 3), (3, 2), (7, 3), (17, 9), (2, 1), (2, 2), (9, 8), (7, 5), (11, 9), (4, 2), (4, 4), (2, 2), (8, 5), (3, 3), (4, 3), (2, 1), (2, 1), (9, 6), (2, 1), (11, 5), (2, 2), (4, 3), (2, 2), (4, 4), (6, 6), (13, 6), (21, 9), (3, 2)]
def allps4 : List (Nat × Nat) := [(14, 4), (2, 2), (4, 1), (2, 7), (30, 4), (31, 10), (6, 9), (10, 2), (8, 3), (3, 1), (4, 2), (4, 8), (4, 2), (6, 4), (5, 1), (4, 3), (34, 16), (7, 2), (9, 4), (1, 4), (5, 9), (17, 11), (32, 2), (1, 2), (1, 2), (1, 1), (6, 3), (12, 1), (1, 3), (2, 3), (2, 3), (3, 1), (17, 6), (2, 2), (1, 1), (6, 1), (2, 1), (2, 1), (20, 5), (5, 1), (13, 7), (1, 1), (21, 7), (2, 2), (4, 5), (7, 3), (4, 2), (4, 1), (9, 9), (1, 5), (17, 25), (5, 3), (4, 11), (7, 9), (7, 3), (4, 1), (1, 1), (2, 12), (5, 2), (15, 12), (1, 17), (2, 3), (16, 4), (2, 3), (6, 2), (1, 1), (2, 2), (3, 9), (6, 2), (6, 2), (6, 3), (12, 3), (14, 2), (1, 2), (12, 3), (2, 1), (9, 1), (2, 19), (5, 1), (11, 3), (1, 2), (1, 1), (33, 5), (6, 2), (1, 1), (26, 16), (4, 1), (4, 1), (4, 4), (3, 3), (6, 7), (21, 16), (5, 3), (5, 2), (18, 13), (3, 1), (2, 2), (5, 1), (2, 4), (2, 2), (19, 4), (4, 1), (1, 1), (3, 2), (4, 2), (15, 9), (10, 29), (17, 9), (1, 2), (38, 8), (2, 9), (1, 6), (3, 2), (1, 1), (4, 5), (1, 1), (1, 1), (3, 2), (1, 4), (4, 1), (3, 2), (5, 3), (13, 1), (16, 2), (7, 4), (4, 1), (2, 3), (11, 1), (3, 1), (2, 1), (1, 1), (7, 1), (1, 3), (17, 2), (2, 1), (6, 8), (7, 7), (2, 1), (3, 6), (5, 2), (1, 1), (2, 1), (6, 2), (10, 1), (1, 3), (11, 5), (2, 1), (2, 8), (5, 5), (1, 1), (2, 1), (1, 3), (10, 2), (22, 13), (3, 2), (1, 1), (2, 1), (6, 6), (16, 11), (6, 1), (3, 5), (2, 1), (3, 2), (5, 2), (7, 2), (2, 5), (9, 1), (2, 2), (2, 10), (1, 1), (1, 1), (2, 1), (12, 23), (8, 1), (3, 2), (7, 1), (1, 1), (4, 4), (5, 5), (10, 2), (1, 2), (5, 3), (2, 2), (20, 4), (1, 6), (2, 1), (6, 5), (20, 3), (11, 10), (1, 1), (3, 3), (3, 2), (7, 3), (17, 9), (2, 5), (1, 7), (2, 1), (2, 2), (9, 8), (7, 5), (2, 3), (1, 1), (8, 3), (11, 9), (1, 2), (1, 4), (4, 1), (4, 2), (3, 1), (1, 3), (4, 6), (4, 4), (2, 2), (1, 1), (8, 5), (3, 1), (42, 11), (17, 2), (3, 4), (3, 3), (1, 1), (4, 3), (2, 1), (6, 9), (1, 2), (4, 1), (1, 2), (15, 3), (2, 1), (8, 2), (9, 6), (2, 1), (5, 10), (2, 5), (4, 1), (11, 5), (1, 11), (19, 10), (8, 9), (2, 2), (4, 3), (2, 2), (19, 5), (4, 1), (3, 1), (4, 4), (6, 6), (6, 1), (6, 7), (3, 1), (13, 6), (1, 2), (8, 2), (1, 3), (20, 1), (4, 10), (21, 9), (3, 2), (13, 1)]
def ms4 : List ℚ := [(7 / 2), (1 / 1), (4 / 1), (2 / 7), (15 / 2), (31 / 10), (2 / 3), (5 / 1), (8 / 3), (3 / 1), (2 / 1), (1 / 2), (2 / 1), (3 / 2), (5 / 1), (4 / 3), (17 / 8), (7 / 2), (9 / 4), (1 / 4), (5 / 9), (17 / 11), (16 / 1), (1 / 2), (1 / 2), (1 / 1), (2 / 1), (12 / 1), (1 / 3), (2 / 3), (2 / 3), (3 / 1), (17 / 6), (1 / 1), (1 / 1), (6 / 1), (2 / 1), (2 / 1), (4 / 1), (5 / 1), (13 / 7), (1 / 1), (3 / 1), (1 / 1), (4 / 5), (7 / 3), (2 / 1), (4 / 1), (1 / 1), (1 / 5), (17 / 25), (5 / 3), (4 / 11), (7 / 9), (7 / 3), (4 / 1), (1 / 1), (1 / 6), (5 / 2), (5 / 4), (1 / 17), (2 / 3), (4 / 1), (2 / 3), (3 / 1), (1 / 1), (1 / 1), (1 / 3), (3 / 1), (3 / 1), (2 / 1), (4 / 1), (7 / 1), (1 / 2), (4 / 1), (2 / 1), (9 / 1), (2 / 19), (5 / 1), (11 / 3), (1 / 2), (1 / 1), (33 / 5), (3 / 1), (1 / 1), (13 / 8), (4 / 1), (4 / 1), (1 / 1), (1 / 1), (6 / 7), (21 / 16), (5 / 3), (5 / 2), (18 / 13), (3 / 1), (1 / 1), (5 / 1), (1 / 2), (1 / 1), (19 / 4), (4 / 1), (1 / 1), (3 / 2), (2 / 1), (5 / 3), (10 / 29), (17 / 9), (1 / 2), (19 / 4), (2 / 9), (1 / 6), (3 / 2), (1 / 1), (4 / 5), (1 / 1), (1 / 1), (3 / 2), (1 / 4), (4 / 1), (3 / 2), (5 / 3), (13 / 1), (8 / 1), (7 / 4), (4 / 1), (2 / 3), (11 / 1), (3 / 1), (2 / 1), (1 / 1), (7 / 1), (1 / 3), (17 / 2), (2 / 1), (3 / 4), (1 / 1), (2 / 1), (1 / 2), (5 / 2), (1 / 1), (2 / 1), (3 / 1), (10 / 1), (1 / 3), (11 / 5), (2 / 1), (1 / 4), (1 / 1), (1 / 1), (2 / 1), (1 / 3), (5 / 1), (22 / 13), (3 / 2), (1 / 1), (2 / 1), (1 / 1), (16 / 11), (6 / 1), (3 / 5), (2 / 1), (3 / 2), (5 / 2), (7 / 2), (2 / 5), (9 / 1), (1 / 1), (1 / 5), (1 / 1), (1 / 1), (2 / 1), (12 / 23), (8 / 1), (3 / 2), (7 / 1), (1 / 1), (1 / 1), (1 / 1), (5 / 1), (1 / 2), (5 / 3), (1 / 1), (5 / 1), (1 / 6), (2 / 1), (6 / 5), (20 / 3), (11 / 10), (1 / 1), (1 / 1), (3 / 2), (7 / 3), (17 / 9), (2 / 5), (1 / 7), (2 / 1), (1 / 1), (9 / 8), (7 / 5), (2 / 3), (1 / 1), (8 / 3), (11 / 9), (1 / 2), (1 / 4), (4 / 1), (2 / 1), (3 / 1), (1 / 3), (2 / 3), (1 / 1), (1 / 1), (1 / 1), (8 / 5), (3 / 1), (42 / 11), (17 / 2), (3 / 4), (1 / 1), (1 / 1), (4 / 3), (2 / 1), (2 / 3), (1 / 2), (4 / 1), (1 / 2), (5 / 1), (2 / 1), (4 / 1), (3 / 2), (2 / 1), (1 / 2), (2 / 5), (4 / 1), (11 / 5), (1 / 11), (19 / 10), (8 / 9), (1 / 1), (4 / 3), (1 / 1), (19 / 5), (4 / 1), (3 / 1), (1 / 1), (1 / 1), (6 / 1), (6 / 7), (3 / 1), (13 / 6), (1 / 2), (4 / 1), (1 / 3), (20 / 1), (2 / 5), (7 / 3), (3 / 2), (13 / 1)]
def aa4 : List ℚ := [56, 4, 4, 14, 120, 310, 54, 20, 24, 3, 8, 32, 8, 24, 5, 12, 544, 14, 36, 4, 45, 187, 64, 2, 2, 1, 18, 12, 3, 6, 6, 3, 102, 4, 1, 6, 2, 2, 100, 5, 91, 1, 147, 4, 20, 21, 8, 4, 81, 5, 425, 15, 44, 63, 21, 4, 1, 24, 10, 180, 17, 6, 64, 6, 12, 1, 4, 27, 12, 12, 18, 36, 28, 2, 36, 2, 9, 38, 5, 33, 2, 1, 165, 12, 1, 416, 4, 4, 16, 9, 42, 336, 15, 10, 234, 3, 4, 5, 8, 4, 76, 4, 1, 6, 8, 135, 290, 153, 2, 304, 18, 6, 6, 1, 20, 1, 1, 6, 4, 4, 6, 15, 13, 32, 28, 4, 6, 11, 3, 2, 1, 7, 3, 34, 2, 48, 49, 2, 18, 10, 1, 2, 12, 10, 3, 55, 2, 16, 25, 1, 2, 3, 20, 286, 6, 1, 2, 36, 176, 6, 15, 2, 6, 10, 14, 10, 9, 4, 20, 1, 1, 2, 276, 8, 6, 7, 1, 16, 25, 20, 2, 15, 4, 80, 6, 2, 30, 60, 110, 1, 9, 6, 21, 153, 10, 7, 2, 4, 72, 35, 6, 1, 24, 99, 2, 4, 4, 8, 3, 3, 24, 16, 4, 1, 40, 3, 462, 34, 12, 9, 1, 12, 2, 54, 2, 4, 2, 45, 2, 16, 54, 2, 50, 10, 4, 55, 11, 190, 72, 4, 12, 4, 95, 4, 3, 16, 36, 6, 42, 3, 78, 2, 16, 3, 20, 40, 189, 6, 13]
theorem pairs4 : pairs matrix 4 3 = allps4 := by kernel_rfl
theorem ms_eq4 : allps4.map (fun p => (p.1 : ℚ) / p.2) = ms4 := by kernel_rfl
theorem aa_eq4 : allps4.map (fun p => ((p.1 * p.2 : Nat) : ℚ)) = aa4 := by kernel_rfl
theorem ms4_length : ms4.length = 259 := by kernel_rfl
theorem ms4_rank0 : rank2 ms4 (1 / 17) = 2 := by kernel_rfl
theorem ms4_keep0 : rankKeep ms4 (1 / 17) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank0]
  decide +kernel
theorem ms4_rank1 : rank2 ms4 (1 / 11) = 4 := by kernel_rfl
theorem ms4_keep1 : rankKeep ms4 (1 / 11) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank1]
  decide +kernel
theorem ms4_rank2 : rank2 ms4 (2 / 19) = 6 := by kernel_rfl
theorem ms4_keep2 : rankKeep ms4 (2 / 19) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank2]
  decide +kernel
theorem ms4_rank3 : rank2 ms4 (1 / 7) = 8 := by kernel_rfl
theorem ms4_keep3 : rankKeep ms4 (1 / 7) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank3]
  decide +kernel
theorem ms4_rank4 : rank2 ms4 (1 / 6) = 12 := by kernel_rfl
theorem ms4_keep4 : rankKeep ms4 (1 / 6) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank4]
  decide +kernel
theorem ms4_rank5 : rank2 ms4 (1 / 5) = 17 := by kernel_rfl
theorem ms4_keep5 : rankKeep ms4 (1 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank5]
  decide +kernel
theorem ms4_rank6 : rank2 ms4 (2 / 9) = 20 := by kernel_rfl
theorem ms4_keep6 : rankKeep ms4 (2 / 9) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank6]
  decide +kernel
theorem ms4_rank7 : rank2 ms4 (1 / 4) = 25 := by kernel_rfl
theorem ms4_keep7 : rankKeep ms4 (1 / 4) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank7]
  decide +kernel
theorem ms4_rank8 : rank2 ms4 (2 / 7) = 30 := by kernel_rfl
theorem ms4_keep8 : rankKeep ms4 (2 / 7) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank8]
  decide +kernel
theorem ms4_rank9 : rank2 ms4 (1 / 3) = 38 := by kernel_rfl
theorem ms4_keep9 : rankKeep ms4 (1 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank9]
  decide +kernel
theorem ms4_rank10 : rank2 ms4 (10 / 29) = 46 := by kernel_rfl
theorem ms4_keep10 : rankKeep ms4 (10 / 29) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank10]
  decide +kernel
theorem ms4_rank11 : rank2 ms4 (4 / 11) = 48 := by kernel_rfl
theorem ms4_keep11 : rankKeep ms4 (4 / 11) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank11]
  decide +kernel
theorem ms4_rank12 : rank2 ms4 (2 / 5) = 53 := by kernel_rfl
theorem ms4_keep12 : rankKeep ms4 (2 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank12]
  decide +kernel
theorem ms4_rank13 : rank2 ms4 (1 / 2) = 71 := by kernel_rfl
theorem ms4_keep13 : rankKeep ms4 (1 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank13]
  decide +kernel
theorem ms4_rank14 : rank2 ms4 (12 / 23) = 86 := by kernel_rfl
theorem ms4_keep14 : rankKeep ms4 (12 / 23) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank14]
  decide +kernel
theorem ms4_rank15 : rank2 ms4 (5 / 9) = 88 := by kernel_rfl
theorem ms4_keep15 : rankKeep ms4 (5 / 9) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank15]
  decide +kernel
theorem ms4_rank16 : rank2 ms4 (3 / 5) = 90 := by kernel_rfl
theorem ms4_keep16 : rankKeep ms4 (3 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank16]
  decide +kernel
theorem ms4_rank17 : rank2 ms4 (2 / 3) = 100 := by kernel_rfl
theorem ms4_keep17 : rankKeep ms4 (2 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank17]
  decide +kernel
theorem ms4_rank18 : rank2 ms4 (17 / 25) = 110 := by kernel_rfl
theorem ms4_keep18 : rankKeep ms4 (17 / 25) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank18]
  decide +kernel
theorem ms4_rank19 : rank2 ms4 (3 / 4) = 113 := by kernel_rfl
theorem ms4_keep19 : rankKeep ms4 (3 / 4) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank19]
  decide +kernel
theorem ms4_rank20 : rank2 ms4 (7 / 9) = 116 := by kernel_rfl
theorem ms4_keep20 : rankKeep ms4 (7 / 9) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank20]
  decide +kernel
theorem ms4_rank21 : rank2 ms4 (4 / 5) = 119 := by kernel_rfl
theorem ms4_keep21 : rankKeep ms4 (4 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank21]
  decide +kernel
theorem ms4_rank22 : rank2 ms4 (6 / 7) = 123 := by kernel_rfl
theorem ms4_keep22 : rankKeep ms4 (6 / 7) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank22]
  decide +kernel
theorem ms4_rank23 : rank2 ms4 (8 / 9) = 126 := by kernel_rfl
theorem ms4_keep23 : rankKeep ms4 (8 / 9) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank23]
  decide +kernel
theorem ms4_rank24 : rank2 ms4 (1 / 1) = 174 := by kernel_rfl
theorem ms4_keep24 : rankKeep ms4 (1 / 1) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank24]
  decide +kernel
theorem ms4_rank25 : rank2 ms4 (11 / 10) = 222 := by kernel_rfl
theorem ms4_keep25 : rankKeep ms4 (11 / 10) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank25]
  decide +kernel
theorem ms4_rank26 : rank2 ms4 (9 / 8) = 224 := by kernel_rfl
theorem ms4_keep26 : rankKeep ms4 (9 / 8) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank26]
  decide +kernel
theorem ms4_rank27 : rank2 ms4 (6 / 5) = 226 := by kernel_rfl
theorem ms4_keep27 : rankKeep ms4 (6 / 5) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank27]
  decide +kernel
theorem ms4_rank28 : rank2 ms4 (11 / 9) = 228 := by kernel_rfl
theorem ms4_keep28 : rankKeep ms4 (11 / 9) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank28]
  decide +kernel
theorem ms4_rank29 : rank2 ms4 (5 / 4) = 230 := by kernel_rfl
theorem ms4_keep29 : rankKeep ms4 (5 / 4) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank29]
  decide +kernel
theorem ms4_rank30 : rank2 ms4 (21 / 16) = 232 := by kernel_rfl
theorem ms4_keep30 : rankKeep ms4 (21 / 16) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank30]
  decide +kernel
theorem ms4_rank31 : rank2 ms4 (4 / 3) = 236 := by kernel_rfl
theorem ms4_keep31 : rankKeep ms4 (4 / 3) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank31]
  decide +kernel
theorem ms4_rank32 : rank2 ms4 (18 / 13) = 240 := by kernel_rfl
theorem ms4_keep32 : rankKeep ms4 (18 / 13) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank32]
  decide +kernel
theorem ms4_rank33 : rank2 ms4 (7 / 5) = 242 := by kernel_rfl
theorem ms4_keep33 : rankKeep ms4 (7 / 5) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank33]
  decide +kernel
theorem ms4_rank34 : rank2 ms4 (16 / 11) = 244 := by kernel_rfl
theorem ms4_keep34 : rankKeep ms4 (16 / 11) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank34]
  decide +kernel
theorem ms4_rank35 : rank2 ms4 (3 / 2) = 256 := by kernel_rfl
theorem ms4_keep35 : rankKeep ms4 (3 / 2) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank35]
  decide +kernel
theorem ms4_rank36 : rank2 ms4 (17 / 11) = 268 := by kernel_rfl
theorem ms4_keep36 : rankKeep ms4 (17 / 11) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank36]
  decide +kernel
theorem ms4_rank37 : rank2 ms4 (8 / 5) = 270 := by kernel_rfl
theorem ms4_keep37 : rankKeep ms4 (8 / 5) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank37]
  decide +kernel
theorem ms4_rank38 : rank2 ms4 (13 / 8) = 272 := by kernel_rfl
theorem ms4_keep38 : rankKeep ms4 (13 / 8) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank38]
  decide +kernel
theorem ms4_rank39 : rank2 ms4 (5 / 3) = 278 := by kernel_rfl
theorem ms4_keep39 : rankKeep ms4 (5 / 3) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank39]
  decide +kernel
theorem ms4_rank40 : rank2 ms4 (22 / 13) = 284 := by kernel_rfl
theorem ms4_keep40 : rankKeep ms4 (22 / 13) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank40]
  decide +kernel
theorem ms4_rank41 : rank2 ms4 (7 / 4) = 286 := by kernel_rfl
theorem ms4_keep41 : rankKeep ms4 (7 / 4) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank41]
  decide +kernel
theorem ms4_rank42 : rank2 ms4 (13 / 7) = 288 := by kernel_rfl
theorem ms4_keep42 : rankKeep ms4 (13 / 7) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank42]
  decide +kernel
theorem ms4_rank43 : rank2 ms4 (17 / 9) = 291 := by kernel_rfl
theorem ms4_keep43 : rankKeep ms4 (17 / 9) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank43]
  decide +kernel
theorem ms4_rank44 : rank2 ms4 (19 / 10) = 294 := by kernel_rfl
theorem ms4_keep44 : rankKeep ms4 (19 / 10) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank44]
  decide +kernel
theorem ms4_rank45 : rank2 ms4 (2 / 1) = 319 := by kernel_rfl
theorem ms4_keep45 : rankKeep ms4 (2 / 1) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank45]
  decide +kernel
theorem ms4_rank46 : rank2 ms4 (17 / 8) = 344 := by kernel_rfl
theorem ms4_keep46 : rankKeep ms4 (17 / 8) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank46]
  decide +kernel
theorem ms4_rank47 : rank2 ms4 (13 / 6) = 346 := by kernel_rfl
theorem ms4_keep47 : rankKeep ms4 (13 / 6) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank47]
  decide +kernel
theorem ms4_rank48 : rank2 ms4 (11 / 5) = 349 := by kernel_rfl
theorem ms4_keep48 : rankKeep ms4 (11 / 5) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank48]
  decide +kernel
theorem ms4_rank49 : rank2 ms4 (9 / 4) = 352 := by kernel_rfl
theorem ms4_keep49 : rankKeep ms4 (9 / 4) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank49]
  decide +kernel
theorem ms4_rank50 : rank2 ms4 (7 / 3) = 357 := by kernel_rfl
theorem ms4_keep50 : rankKeep ms4 (7 / 3) 3 10 = true := by
  unfold rankKeep
  rw [ms4_length, ms4_rank50]
  decide +kernel
theorem ms4_rank51 : rank2 ms4 (5 / 2) = 365 := by kernel_rfl
theorem ms4_keep51 : rankKeep ms4 (5 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank51]
  decide +kernel
theorem ms4_rank52 : rank2 ms4 (8 / 3) = 371 := by kernel_rfl
theorem ms4_keep52 : rankKeep ms4 (8 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank52]
  decide +kernel
theorem ms4_rank53 : rank2 ms4 (17 / 6) = 374 := by kernel_rfl
theorem ms4_keep53 : rankKeep ms4 (17 / 6) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank53]
  decide +kernel
theorem ms4_rank54 : rank2 ms4 (3 / 1) = 389 := by kernel_rfl
theorem ms4_keep54 : rankKeep ms4 (3 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank54]
  decide +kernel
theorem ms4_rank55 : rank2 ms4 (31 / 10) = 404 := by kernel_rfl
theorem ms4_keep55 : rankKeep ms4 (31 / 10) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank55]
  decide +kernel
theorem ms4_rank56 : rank2 ms4 (7 / 2) = 408 := by kernel_rfl
theorem ms4_keep56 : rankKeep ms4 (7 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank56]
  decide +kernel
theorem ms4_rank57 : rank2 ms4 (11 / 3) = 412 := by kernel_rfl
theorem ms4_keep57 : rankKeep ms4 (11 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank57]
  decide +kernel
theorem ms4_rank58 : rank2 ms4 (19 / 5) = 414 := by kernel_rfl
theorem ms4_keep58 : rankKeep ms4 (19 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank58]
  decide +kernel
theorem ms4_rank59 : rank2 ms4 (42 / 11) = 416 := by kernel_rfl
theorem ms4_keep59 : rankKeep ms4 (42 / 11) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank59]
  decide +kernel
theorem ms4_rank60 : rank2 ms4 (4 / 1) = 435 := by kernel_rfl
theorem ms4_keep60 : rankKeep ms4 (4 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank60]
  decide +kernel
theorem ms4_rank61 : rank2 ms4 (19 / 4) = 455 := by kernel_rfl
theorem ms4_keep61 : rankKeep ms4 (19 / 4) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank61]
  decide +kernel
theorem ms4_rank62 : rank2 ms4 (5 / 1) = 466 := by kernel_rfl
theorem ms4_keep62 : rankKeep ms4 (5 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank62]
  decide +kernel
theorem ms4_rank63 : rank2 ms4 (6 / 1) = 478 := by kernel_rfl
theorem ms4_keep63 : rankKeep ms4 (6 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank63]
  decide +kernel
theorem ms4_rank64 : rank2 ms4 (33 / 5) = 482 := by kernel_rfl
theorem ms4_keep64 : rankKeep ms4 (33 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank64]
  decide +kernel
theorem ms4_rank65 : rank2 ms4 (20 / 3) = 484 := by kernel_rfl
theorem ms4_keep65 : rankKeep ms4 (20 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank65]
  decide +kernel
theorem ms4_rank66 : rank2 ms4 (7 / 1) = 488 := by kernel_rfl
theorem ms4_keep66 : rankKeep ms4 (7 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank66]
  decide +kernel
theorem ms4_rank67 : rank2 ms4 (15 / 2) = 492 := by kernel_rfl
theorem ms4_keep67 : rankKeep ms4 (15 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank67]
  decide +kernel
theorem ms4_rank68 : rank2 ms4 (8 / 1) = 495 := by kernel_rfl
theorem ms4_keep68 : rankKeep ms4 (8 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank68]
  decide +kernel
theorem ms4_rank69 : rank2 ms4 (17 / 2) = 499 := by kernel_rfl
theorem ms4_keep69 : rankKeep ms4 (17 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank69]
  decide +kernel
theorem ms4_rank70 : rank2 ms4 (9 / 1) = 503 := by kernel_rfl
theorem ms4_keep70 : rankKeep ms4 (9 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank70]
  decide +kernel
theorem ms4_rank71 : rank2 ms4 (10 / 1) = 506 := by kernel_rfl
theorem ms4_keep71 : rankKeep ms4 (10 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank71]
  decide +kernel
theorem ms4_rank72 : rank2 ms4 (11 / 1) = 508 := by kernel_rfl
theorem ms4_keep72 : rankKeep ms4 (11 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank72]
  decide +kernel
theorem ms4_rank73 : rank2 ms4 (12 / 1) = 510 := by kernel_rfl
theorem ms4_keep73 : rankKeep ms4 (12 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank73]
  decide +kernel
theorem ms4_rank74 : rank2 ms4 (13 / 1) = 513 := by kernel_rfl
theorem ms4_keep74 : rankKeep ms4 (13 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank74]
  decide +kernel
theorem ms4_rank75 : rank2 ms4 (16 / 1) = 516 := by kernel_rfl
theorem ms4_keep75 : rankKeep ms4 (16 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank75]
  decide +kernel
theorem ms4_rank76 : rank2 ms4 (20 / 1) = 518 := by kernel_rfl
theorem ms4_keep76 : rankKeep ms4 (20 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms4_length, ms4_rank76]
  decide +kernel
theorem aa4_length : aa4.length = 259 := by kernel_rfl
theorem aa4_rank0 : rank2 aa4 (1 / 1) = 23 := by kernel_rfl
theorem aa4_keep0 : rankKeep aa4 (1 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa4_length, aa4_rank0]
  decide +kernel
theorem aa4_rank1 : rank2 aa4 (2 / 1) = 72 := by kernel_rfl
theorem aa4_keep1 : rankKeep aa4 (2 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank1]
  decide +kernel
theorem aa4_rank2 : rank2 aa4 (3 / 1) = 113 := by kernel_rfl
theorem aa4_keep2 : rankKeep aa4 (3 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank2]
  decide +kernel
theorem aa4_rank3 : rank2 aa4 (4 / 1) = 154 := by kernel_rfl
theorem aa4_keep3 : rankKeep aa4 (4 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank3]
  decide +kernel
theorem aa4_rank4 : rank2 aa4 (5 / 1) = 186 := by kernel_rfl
theorem aa4_keep4 : rankKeep aa4 (5 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank4]
  decide +kernel
theorem aa4_rank5 : rank2 aa4 (6 / 1) = 211 := by kernel_rfl
theorem aa4_keep5 : rankKeep aa4 (6 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank5]
  decide +kernel
theorem aa4_rank6 : rank2 aa4 (7 / 1) = 234 := by kernel_rfl
theorem aa4_keep6 : rankKeep aa4 (7 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank6]
  decide +kernel
theorem aa4_rank7 : rank2 aa4 (8 / 1) = 244 := by kernel_rfl
theorem aa4_keep7 : rankKeep aa4 (8 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank7]
  decide +kernel
theorem aa4_rank8 : rank2 aa4 (9 / 1) = 256 := by kernel_rfl
theorem aa4_keep8 : rankKeep aa4 (9 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank8]
  decide +kernel
theorem aa4_rank9 : rank2 aa4 (10 / 1) = 269 := by kernel_rfl
theorem aa4_keep9 : rankKeep aa4 (10 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank9]
  decide +kernel
theorem aa4_rank10 : rank2 aa4 (11 / 1) = 279 := by kernel_rfl
theorem aa4_keep10 : rankKeep aa4 (11 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank10]
  decide +kernel
theorem aa4_rank11 : rank2 aa4 (12 / 1) = 291 := by kernel_rfl
theorem aa4_keep11 : rankKeep aa4 (12 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank11]
  decide +kernel
theorem aa4_rank12 : rank2 aa4 (13 / 1) = 303 := by kernel_rfl
theorem aa4_keep12 : rankKeep aa4 (13 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank12]
  decide +kernel
theorem aa4_rank13 : rank2 aa4 (14 / 1) = 308 := by kernel_rfl
theorem aa4_keep13 : rankKeep aa4 (14 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank13]
  decide +kernel
theorem aa4_rank14 : rank2 aa4 (15 / 1) = 316 := by kernel_rfl
theorem aa4_keep14 : rankKeep aa4 (15 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank14]
  decide +kernel
theorem aa4_rank15 : rank2 aa4 (16 / 1) = 328 := by kernel_rfl
theorem aa4_keep15 : rankKeep aa4 (16 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank15]
  decide +kernel
theorem aa4_rank16 : rank2 aa4 (17 / 1) = 336 := by kernel_rfl
theorem aa4_keep16 : rankKeep aa4 (17 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank16]
  decide +kernel
theorem aa4_rank17 : rank2 aa4 (18 / 1) = 341 := by kernel_rfl
theorem aa4_keep17 : rankKeep aa4 (18 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank17]
  decide +kernel
theorem aa4_rank18 : rank2 aa4 (20 / 1) = 352 := by kernel_rfl
theorem aa4_keep18 : rankKeep aa4 (20 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank18]
  decide +kernel
theorem aa4_rank19 : rank2 aa4 (21 / 1) = 362 := by kernel_rfl
theorem aa4_keep19 : rankKeep aa4 (21 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank19]
  decide +kernel
theorem aa4_rank20 : rank2 aa4 (24 / 1) = 370 := by kernel_rfl
theorem aa4_keep20 : rankKeep aa4 (24 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank20]
  decide +kernel
theorem aa4_rank21 : rank2 aa4 (25 / 1) = 377 := by kernel_rfl
theorem aa4_keep21 : rankKeep aa4 (25 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank21]
  decide +kernel
theorem aa4_rank22 : rank2 aa4 (27 / 1) = 380 := by kernel_rfl
theorem aa4_keep22 : rankKeep aa4 (27 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank22]
  decide +kernel
theorem aa4_rank23 : rank2 aa4 (28 / 1) = 383 := by kernel_rfl
theorem aa4_keep23 : rankKeep aa4 (28 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank23]
  decide +kernel
theorem aa4_rank24 : rank2 aa4 (30 / 1) = 386 := by kernel_rfl
theorem aa4_keep24 : rankKeep aa4 (30 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank24]
  decide +kernel
theorem aa4_rank25 : rank2 aa4 (32 / 1) = 389 := by kernel_rfl
theorem aa4_keep25 : rankKeep aa4 (32 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank25]
  decide +kernel
theorem aa4_rank26 : rank2 aa4 (33 / 1) = 392 := by kernel_rfl
theorem aa4_keep26 : rankKeep aa4 (33 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank26]
  decide +kernel
theorem aa4_rank27 : rank2 aa4 (34 / 1) = 395 := by kernel_rfl
theorem aa4_keep27 : rankKeep aa4 (34 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank27]
  decide +kernel
theorem aa4_rank28 : rank2 aa4 (35 / 1) = 398 := by kernel_rfl
theorem aa4_keep28 : rankKeep aa4 (35 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank28]
  decide +kernel
theorem aa4_rank29 : rank2 aa4 (36 / 1) = 404 := by kernel_rfl
theorem aa4_keep29 : rankKeep aa4 (36 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank29]
  decide +kernel
theorem aa4_rank30 : rank2 aa4 (38 / 1) = 410 := by kernel_rfl
theorem aa4_keep30 : rankKeep aa4 (38 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank30]
  decide +kernel
theorem aa4_rank31 : rank2 aa4 (40 / 1) = 413 := by kernel_rfl
theorem aa4_keep31 : rankKeep aa4 (40 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank31]
  decide +kernel
theorem aa4_rank32 : rank2 aa4 (42 / 1) = 417 := by kernel_rfl
theorem aa4_keep32 : rankKeep aa4 (42 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank32]
  decide +kernel
theorem aa4_rank33 : rank2 aa4 (44 / 1) = 420 := by kernel_rfl
theorem aa4_keep33 : rankKeep aa4 (44 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank33]
  decide +kernel
theorem aa4_rank34 : rank2 aa4 (45 / 1) = 423 := by kernel_rfl
theorem aa4_keep34 : rankKeep aa4 (45 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank34]
  decide +kernel
theorem aa4_rank35 : rank2 aa4 (48 / 1) = 426 := by kernel_rfl
theorem aa4_keep35 : rankKeep aa4 (48 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank35]
  decide +kernel
theorem aa4_rank36 : rank2 aa4 (49 / 1) = 428 := by kernel_rfl
theorem aa4_keep36 : rankKeep aa4 (49 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank36]
  decide +kernel
theorem aa4_rank37 : rank2 aa4 (50 / 1) = 430 := by kernel_rfl
theorem aa4_keep37 : rankKeep aa4 (50 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank37]
  decide +kernel
theorem aa4_rank38 : rank2 aa4 (54 / 1) = 434 := by kernel_rfl
theorem aa4_keep38 : rankKeep aa4 (54 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank38]
  decide +kernel
theorem aa4_rank39 : rank2 aa4 (55 / 1) = 439 := by kernel_rfl
theorem aa4_keep39 : rankKeep aa4 (55 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank39]
  decide +kernel
theorem aa4_rank40 : rank2 aa4 (56 / 1) = 442 := by kernel_rfl
theorem aa4_keep40 : rankKeep aa4 (56 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank40]
  decide +kernel
theorem aa4_rank41 : rank2 aa4 (60 / 1) = 444 := by kernel_rfl
theorem aa4_keep41 : rankKeep aa4 (60 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank41]
  decide +kernel
theorem aa4_rank42 : rank2 aa4 (63 / 1) = 446 := by kernel_rfl
theorem aa4_keep42 : rankKeep aa4 (63 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank42]
  decide +kernel
theorem aa4_rank43 : rank2 aa4 (64 / 1) = 449 := by kernel_rfl
theorem aa4_keep43 : rankKeep aa4 (64 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank43]
  decide +kernel
theorem aa4_rank44 : rank2 aa4 (72 / 1) = 453 := by kernel_rfl
theorem aa4_keep44 : rankKeep aa4 (72 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank44]
  decide +kernel
theorem aa4_rank45 : rank2 aa4 (76 / 1) = 456 := by kernel_rfl
theorem aa4_keep45 : rankKeep aa4 (76 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank45]
  decide +kernel
theorem aa4_rank46 : rank2 aa4 (78 / 1) = 458 := by kernel_rfl
theorem aa4_keep46 : rankKeep aa4 (78 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank46]
  decide +kernel
theorem aa4_rank47 : rank2 aa4 (80 / 1) = 460 := by kernel_rfl
theorem aa4_keep47 : rankKeep aa4 (80 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank47]
  decide +kernel
theorem aa4_rank48 : rank2 aa4 (81 / 1) = 462 := by kernel_rfl
theorem aa4_keep48 : rankKeep aa4 (81 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank48]
  decide +kernel
theorem aa4_rank49 : rank2 aa4 (91 / 1) = 464 := by kernel_rfl
theorem aa4_keep49 : rankKeep aa4 (91 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank49]
  decide +kernel
theorem aa4_rank50 : rank2 aa4 (95 / 1) = 466 := by kernel_rfl
theorem aa4_keep50 : rankKeep aa4 (95 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank50]
  decide +kernel
theorem aa4_rank51 : rank2 aa4 (99 / 1) = 468 := by kernel_rfl
theorem aa4_keep51 : rankKeep aa4 (99 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank51]
  decide +kernel
theorem aa4_rank52 : rank2 aa4 (100 / 1) = 470 := by kernel_rfl
theorem aa4_keep52 : rankKeep aa4 (100 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank52]
  decide +kernel
theorem aa4_rank53 : rank2 aa4 (102 / 1) = 472 := by kernel_rfl
theorem aa4_keep53 : rankKeep aa4 (102 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank53]
  decide +kernel
theorem aa4_rank54 : rank2 aa4 (110 / 1) = 474 := by kernel_rfl
theorem aa4_keep54 : rankKeep aa4 (110 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank54]
  decide +kernel
theorem aa4_rank55 : rank2 aa4 (120 / 1) = 476 := by kernel_rfl
theorem aa4_keep55 : rankKeep aa4 (120 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank55]
  decide +kernel
theorem aa4_rank56 : rank2 aa4 (135 / 1) = 478 := by kernel_rfl
theorem aa4_keep56 : rankKeep aa4 (135 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank56]
  decide +kernel
theorem aa4_rank57 : rank2 aa4 (147 / 1) = 480 := by kernel_rfl
theorem aa4_keep57 : rankKeep aa4 (147 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank57]
  decide +kernel
theorem aa4_rank58 : rank2 aa4 (153 / 1) = 483 := by kernel_rfl
theorem aa4_keep58 : rankKeep aa4 (153 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank58]
  decide +kernel
theorem aa4_rank59 : rank2 aa4 (165 / 1) = 486 := by kernel_rfl
theorem aa4_keep59 : rankKeep aa4 (165 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank59]
  decide +kernel
theorem aa4_rank60 : rank2 aa4 (176 / 1) = 488 := by kernel_rfl
theorem aa4_keep60 : rankKeep aa4 (176 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank60]
  decide +kernel
theorem aa4_rank61 : rank2 aa4 (180 / 1) = 490 := by kernel_rfl
theorem aa4_keep61 : rankKeep aa4 (180 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank61]
  decide +kernel
theorem aa4_rank62 : rank2 aa4 (187 / 1) = 492 := by kernel_rfl
theorem aa4_keep62 : rankKeep aa4 (187 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank62]
  decide +kernel
theorem aa4_rank63 : rank2 aa4 (189 / 1) = 494 := by kernel_rfl
theorem aa4_keep63 : rankKeep aa4 (189 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa4_length, aa4_rank63]
  decide +kernel
theorem aa4_rank64 : rank2 aa4 (190 / 1) = 496 := by kernel_rfl
theorem aa4_keep64 : rankKeep aa4 (190 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa4_length, aa4_rank64]
  decide +kernel
theorem aa4_rank65 : rank2 aa4 (234 / 1) = 498 := by kernel_rfl
theorem aa4_keep65 : rankKeep aa4 (234 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa4_length, aa4_rank65]
  decide +kernel
theorem aa4_rank66 : rank2 aa4 (276 / 1) = 500 := by kernel_rfl
theorem aa4_keep66 : rankKeep aa4 (276 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa4_length, aa4_rank66]
  decide +kernel
theorem aa4_rank67 : rank2 aa4 (286 / 1) = 502 := by kernel_rfl
theorem aa4_keep67 : rankKeep aa4 (286 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa4_length, aa4_rank67]
  decide +kernel
theorem aa4_rank68 : rank2 aa4 (290 / 1) = 504 := by kernel_rfl
theorem aa4_keep68 : rankKeep aa4 (290 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa4_length, aa4_rank68]
  decide +kernel
theorem aa4_rank69 : rank2 aa4 (304 / 1) = 506 := by kernel_rfl
theorem aa4_keep69 : rankKeep aa4 (304 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa4_length, aa4_rank69]
  decide +kernel
theorem aa4_rank70 : rank2 aa4 (310 / 1) = 508 := by kernel_rfl
theorem aa4_keep70 : rankKeep aa4 (310 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa4_length, aa4_rank70]
  decide +kernel
theorem aa4_rank71 : rank2 aa4 (336 / 1) = 510 := by kernel_rfl
theorem aa4_keep71 : rankKeep aa4 (336 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa4_length, aa4_rank71]
  decide +kernel
theorem aa4_rank72 : rank2 aa4 (416 / 1) = 512 := by kernel_rfl
theorem aa4_keep72 : rankKeep aa4 (416 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa4_length, aa4_rank72]
  decide +kernel
theorem aa4_rank73 : rank2 aa4 (425 / 1) = 514 := by kernel_rfl
theorem aa4_keep73 : rankKeep aa4 (425 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa4_length, aa4_rank73]
  decide +kernel
theorem aa4_rank74 : rank2 aa4 (462 / 1) = 516 := by kernel_rfl
theorem aa4_keep74 : rankKeep aa4 (462 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa4_length, aa4_rank74]
  decide +kernel
theorem aa4_rank75 : rank2 aa4 (544 / 1) = 518 := by kernel_rfl
theorem aa4_keep75 : rankKeep aa4 (544 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa4_length, aa4_rank75]
  decide +kernel
end Proofs.Witness
