import Proofs.WitnessData
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Proofs.Witness
def ps1 : List (Nat × Nat) := [(4, 4), (1, 2), (2, 3), (1, 2), (3, 4), (2, 3), (2, 2), (7, 9), (2, 2), (1, 2), (1, 1), (3, 3), (3, 3), (1, 1), (5, 6), (2, 2), (1, 2), (1, 1), (1, 1), (4, 7), (1, 2), (3, 3), (1, 1), (2, 2), (1, 2), (2, 3), (1, 2), (3, 3), (1, 2), (1, 1), (4, 5), (1, 2), (1, 1), (1, 1), (1, 1), (2, 2), (1, 1), (3, 4), (3, 6), (1, 1), (2, 2), (1, 1), (3, 3), (1, 1), (1, 1), (3, 6), (1, 2), (2, 3), (4, 6), (3, 5), (1, 1), (1, 1), (1, 2), (3, 4), (4, 6), (3, 4), (3, 5), (2, 3), (4, 4), (1, 1), (1, 2), (4, 5), (4, 7), (1, 2), (1, 1), (1, 1), (5, 6), (4, 5), (1, 1), (3, 3), (1, 1), (2, 2), (1, 2), (7, 9), (1, 2), (1, 1), (1, 1), (1, 1), (4, 6)]
def allps1 : List (Nat × Nat) := [(4, 4), (1, 2), (4, 10), (2, 3), (2, 1), (3, 2), (3, 8), (1, 2), (3, 4), (2, 3), (11, 16), (2, 2), (1, 4), (7, 9), (1, 11), (2, 2), (1, 2), (4, 2), (1, 1), (3, 3), (3, 3), (1, 1), (5, 6), (2, 2), (1, 2), (1, 1), (4, 1), (9, 5), (1, 1), (4, 7), (10, 7), (3, 2), (1, 5), (1, 2), (5, 1), (2, 5), (18, 25), (1, 11), (1, 9), (3, 3), (1, 1), (2, 12), (2, 2), (3, 12), (4, 17), (5, 4), (1, 2), (2, 3), (1, 2), (2, 9), (3, 2), (4, 2), (3, 3), (1, 2), (1, 3), (1, 1), (3, 1), (2, 19), (1, 3), (4, 5), (1, 2), (1, 1), (2, 1), (5, 16), (1, 1), (1, 3), (2, 7), (5, 16), (4, 3), (2, 13), (1, 1), (2, 2), (1, 1), (3, 4), (3, 2), (3, 9), (6, 29), (1, 9), (2, 8), (1, 9), (3, 6), (2, 1), (1, 5), (2, 1), (1, 1), (2, 2), (1, 4), (1, 1), (5, 3), (11, 1), (4, 2), (1, 4), (2, 1), (3, 3), (1, 1), (3, 1), (3, 2), (1, 1), (3, 1), (1, 8), (2, 1), (3, 6), (1, 2), (2, 1), (3, 1), (2, 5), (3, 8), (1, 5), (2, 3), (3, 2), (3, 13), (5, 2), (2, 1), (4, 6), (1, 11), (2, 1), (3, 5), (3, 2), (6, 2), (1, 1), (2, 5), (2, 1), (2, 10), (1, 1), (2, 23), (2, 1), (2, 1), (1, 4), (1, 4), (1, 5), (9, 2), (4, 3), (1, 2), (3, 4), (4, 6), (3, 1), (3, 4), (3, 5), (2, 3), (4, 4), (2, 10), (1, 1), (1, 3), (1, 2), (1, 3), (2, 9), (4, 5), (4, 7), (1, 2), (3, 8), (2, 5), (1, 3), (3, 9), (1, 4), (1, 1), (1, 1), (2, 1), (5, 6), (6, 4), (4, 5), (1, 1), (4, 11), (6, 2), (1, 4), (3, 3), (1, 3), (1, 1), (2, 9), (2, 2), (1, 2), (1, 3), (1, 6), (7, 10), (1, 5), (1, 11), (10, 10), (7, 9), (1, 2), (4, 3), (1, 1), (2, 5), (2, 1), (1, 1), (6, 4), (7, 6), (2, 1), (2, 7), (1, 1), (4, 6), (7, 2), (6, 3), (2, 1), (3, 10), (2, 9), (2, 1)]
def ms1 : List ℚ := [(1 / 1), (1 / 2), (2 / 5), (2 / 3), (2 / 1), (3 / 2), (3 / 8), (1 / 2), (3 / 4), (2 / 3), (11 / 16), (1 / 1), (1 / 4), (7 / 9), (1 / 11), (1 / 1), (1 / 2), (2 / 1), (1 / 1), (1 / 1), (1 / 1), (1 / 1), (5 / 6), (1 / 1), (1 / 2), (1 / 1), (4 / 1), (9 / 5), (1 / 1), (4 / 7), (10 / 7), (3 / 2), (1 / 5), (1 / 2), (5 / 1), (2 / 5), (18 / 25), (1 / 11), (1 / 9), (1 / 1), (1 / 1), (1 / 6), (1 / 1), (1 / 4), (4 / 17), (5 / 4), (1 / 2), (2 / 3), (1 / 2), (2 / 9), (3 / 2), (2 / 1), (1 / 1), (1 / 2), (1 / 3), (1 / 1), (3 / 1), (2 / 19), (1 / 3), (4 / 5), (1 / 2), (1 / 1), (2 / 1), (5 / 16), (1 / 1), (1 / 3), (2 / 7), (5 / 16), (4 / 3), (2 / 13), (1 / 1), (1 / 1), (1 / 1), (3 / 4), (3 / 2), (1 / 3), (6 / 29), (1 / 9), (1 / 4), (1 / 9), (1 / 2), (2 / 1), (1 / 5), (2 / 1), (1 / 1), (1 / 1), (1 / 4), (1 / 1), (5 / 3), (11 / 1), (2 / 1), (1 / 4), (2 / 1), (1 / 1), (1 / 1), (3 / 1), (3 / 2), (1 / 1), (3 / 1), (1 / 8), (2 / 1), (1 / 2), (1 / 2), (2 / 1), (3 / 1), (2 / 5), (3 / 8), (1 / 5), (2 / 3), (3 / 2), (3 / 13), (5 / 2), (2 / 1), (2 / 3), (1 / 11), (2 / 1), (3 / 5), (3 / 2), (3 / 1), (1 / 1), (2 / 5), (2 / 1), (1 / 5), (1 / 1), (2 / 23), (2 / 1), (2 / 1), (1 / 4), (1 / 4), (1 / 5), (9 / 2), (4 / 3), (1 / 2), (3 / 4), (2 / 3), (3 / 1), (3 / 4), (3 / 5), (2 / 3), (1 / 1), (1 / 5), (1 / 1), (1 / 3), (1 / 2), (1 / 3), (2 / 9), (4 / 5), (4 / 7), (1 / 2), (3 / 8), (2 / 5), (1 / 3), (1 / 3), (1 / 4), (1 / 1), (1 / 1), (2 / 1), (5 / 6), (3 / 2), (4 / 5), (1 / 1), (4 / 11), (3 / 1), (1 / 4), (1 / 1), (1 / 3), (1 / 1), (2 / 9), (1 / 1), (1 / 2), (1 / 3), (1 / 6), (7 / 10), (1 / 5), (1 / 11), (1 / 1), (7 / 9), (1 / 2), (4 / 3), (1 / 1), (2 / 5), (2 / 1), (1 / 1), (3 / 2), (7 / 6), (2 / 1), (2 / 7), (1 / 1), (2 / 3), (7 / 2), (2 / 1), (2 / 1), (3 / 10), (2 / 9), (2 / 1)]
def aa1 : List ℚ := [16, 2, 40, 6, 2, 6, 24, 2, 12, 6, 176, 4, 4, 63, 11, 4, 2, 8, 1, 9, 9, 1, 30, 4, 2, 1, 4, 45, 1, 28, 70, 6, 5, 2, 5, 10, 450, 11, 9, 9, 1, 24, 4, 36, 68, 20, 2, 6, 2, 18, 6, 8, 9, 2, 3, 1, 3, 38, 3, 20, 2, 1, 2, 80, 1, 3, 14, 80, 12, 26, 1, 4, 1, 12, 6, 27, 174, 9, 16, 9, 18, 2, 5, 2, 1, 4, 4, 1, 15, 11, 8, 4, 2, 9, 1, 3, 6, 1, 3, 8, 2, 18, 2, 2, 3, 10, 24, 5, 6, 6, 39, 10, 2, 24, 11, 2, 15, 6, 12, 1, 10, 2, 20, 1, 46, 2, 2, 4, 4, 5, 18, 12, 2, 12, 24, 3, 12, 15, 6, 16, 20, 1, 3, 2, 3, 18, 20, 28, 2, 24, 10, 3, 27, 4, 1, 1, 2, 30, 24, 20, 1, 44, 12, 4, 9, 3, 1, 18, 4, 2, 3, 6, 70, 5, 11, 100, 63, 2, 12, 1, 10, 2, 1, 24, 42, 2, 14, 1, 24, 14, 18, 2, 30, 18, 2]
theorem pairs1 : pairs matrix 1 3 = allps1 := by kernel_rfl
theorem ms_eq1 : allps1.map (fun p => (p.1 : ℚ) / p.2) = ms1 := by kernel_rfl
theorem aa_eq1 : allps1.map (fun p => ((p.1 * p.2 : Nat) : ℚ)) = aa1 := by kernel_rfl
theorem ms1_length : ms1.length = 195 := by kernel_rfl
theorem ms1_rank0 : rank2 ms1 (2 / 23) = 2 := by kernel_rfl
theorem ms1_keep0 : rankKeep ms1 (2 / 23) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank0]
  decide +kernel
theorem ms1_rank1 : rank2 ms1 (1 / 11) = 7 := by kernel_rfl
theorem ms1_keep1 : rankKeep ms1 (1 / 11) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank1]
  decide +kernel
theorem ms1_rank2 : rank2 ms1 (2 / 19) = 12 := by kernel_rfl
theorem ms1_keep2 : rankKeep ms1 (2 / 19) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank2]
  decide +kernel
theorem ms1_rank3 : rank2 ms1 (1 / 9) = 16 := by kernel_rfl
theorem ms1_keep3 : rankKeep ms1 (1 / 9) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank3]
  decide +kernel
theorem ms1_rank4 : rank2 ms1 (1 / 8) = 20 := by kernel_rfl
theorem ms1_keep4 : rankKeep ms1 (1 / 8) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank4]
  decide +kernel
theorem ms1_rank5 : rank2 ms1 (2 / 13) = 22 := by kernel_rfl
theorem ms1_keep5 : rankKeep ms1 (2 / 13) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank5]
  decide +kernel
theorem ms1_rank6 : rank2 ms1 (1 / 6) = 25 := by kernel_rfl
theorem ms1_keep6 : rankKeep ms1 (1 / 6) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank6]
  decide +kernel
theorem ms1_rank7 : rank2 ms1 (1 / 5) = 34 := by kernel_rfl
theorem ms1_keep7 : rankKeep ms1 (1 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank7]
  decide +kernel
theorem ms1_rank8 : rank2 ms1 (6 / 29) = 42 := by kernel_rfl
theorem ms1_keep8 : rankKeep ms1 (6 / 29) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank8]
  decide +kernel
theorem ms1_rank9 : rank2 ms1 (2 / 9) = 47 := by kernel_rfl
theorem ms1_keep9 : rankKeep ms1 (2 / 9) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank9]
  decide +kernel
theorem ms1_rank10 : rank2 ms1 (3 / 13) = 52 := by kernel_rfl
theorem ms1_keep10 : rankKeep ms1 (3 / 13) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank10]
  decide +kernel
theorem ms1_rank11 : rank2 ms1 (4 / 17) = 54 := by kernel_rfl
theorem ms1_keep11 : rankKeep ms1 (4 / 17) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank11]
  decide +kernel
theorem ms1_rank12 : rank2 ms1 (1 / 4) = 64 := by kernel_rfl
theorem ms1_keep12 : rankKeep ms1 (1 / 4) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank12]
  decide +kernel
theorem ms1_rank13 : rank2 ms1 (2 / 7) = 75 := by kernel_rfl
theorem ms1_keep13 : rankKeep ms1 (2 / 7) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank13]
  decide +kernel
theorem ms1_rank14 : rank2 ms1 (3 / 10) = 78 := by kernel_rfl
theorem ms1_keep14 : rankKeep ms1 (3 / 10) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank14]
  decide +kernel
theorem ms1_rank15 : rank2 ms1 (5 / 16) = 81 := by kernel_rfl
theorem ms1_keep15 : rankKeep ms1 (5 / 16) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank15]
  decide +kernel
theorem ms1_rank16 : rank2 ms1 (1 / 3) = 93 := by kernel_rfl
theorem ms1_keep16 : rankKeep ms1 (1 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank16]
  decide +kernel
theorem ms1_rank17 : rank2 ms1 (4 / 11) = 104 := by kernel_rfl
theorem ms1_keep17 : rankKeep ms1 (4 / 11) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank17]
  decide +kernel
theorem ms1_rank18 : rank2 ms1 (3 / 8) = 108 := by kernel_rfl
theorem ms1_keep18 : rankKeep ms1 (3 / 8) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank18]
  decide +kernel
theorem ms1_rank19 : rank2 ms1 (2 / 5) = 117 := by kernel_rfl
theorem ms1_keep19 : rankKeep ms1 (2 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank19]
  decide +kernel
theorem ms1_rank20 : rank2 ms1 (1 / 2) = 140 := by kernel_rfl
theorem ms1_keep20 : rankKeep ms1 (1 / 2) 3 10 = true := by
  unfold rankKeep
  rw [ms1_length, ms1_rank20]
  decide +kernel
theorem ms1_rank21 : rank2 ms1 (4 / 7) = 159 := by kernel_rfl
theorem ms1_keep21 : rankKeep ms1 (4 / 7) 3 10 = true := by
  unfold rankKeep
  rw [ms1_length, ms1_rank21]
  decide +kernel
theorem ms1_rank22 : rank2 ms1 (3 / 5) = 163 := by kernel_rfl
theorem ms1_keep22 : rankKeep ms1 (3 / 5) 3 10 = true := by
  unfold rankKeep
  rw [ms1_length, ms1_rank22]
  decide +kernel
theorem ms1_rank23 : rank2 ms1 (2 / 3) = 173 := by kernel_rfl
theorem ms1_keep23 : rankKeep ms1 (2 / 3) 3 10 = true := by
  unfold rankKeep
  rw [ms1_length, ms1_rank23]
  decide +kernel
theorem ms1_rank24 : rank2 ms1 (11 / 16) = 182 := by kernel_rfl
theorem ms1_keep24 : rankKeep ms1 (11 / 16) 3 10 = true := by
  unfold rankKeep
  rw [ms1_length, ms1_rank24]
  decide +kernel
theorem ms1_rank25 : rank2 ms1 (7 / 10) = 184 := by kernel_rfl
theorem ms1_keep25 : rankKeep ms1 (7 / 10) 3 10 = true := by
  unfold rankKeep
  rw [ms1_length, ms1_rank25]
  decide +kernel
theorem ms1_rank26 : rank2 ms1 (18 / 25) = 186 := by kernel_rfl
theorem ms1_keep26 : rankKeep ms1 (18 / 25) 3 10 = true := by
  unfold rankKeep
  rw [ms1_length, ms1_rank26]
  decide +kernel
theorem ms1_rank27 : rank2 ms1 (3 / 4) = 191 := by kernel_rfl
theorem ms1_keep27 : rankKeep ms1 (3 / 4) 3 10 = true := by
  unfold rankKeep
  rw [ms1_length, ms1_rank27]
  decide +kernel
theorem ms1_rank28 : rank2 ms1 (7 / 9) = 197 := by kernel_rfl
theorem ms1_keep28 : rankKeep ms1 (7 / 9) 3 10 = true := by
  unfold rankKeep
  rw [ms1_length, ms1_rank28]
  decide +kernel
theorem ms1_rank29 : rank2 ms1 (4 / 5) = 202 := by kernel_rfl
theorem ms1_keep29 : rankKeep ms1 (4 / 5) 3 10 = true := by
  unfold rankKeep
  rw [ms1_length, ms1_rank29]
  decide +kernel
theorem ms1_rank30 : rank2 ms1 (5 / 6) = 207 := by kernel_rfl
theorem ms1_keep30 : rankKeep ms1 (5 / 6) 3 10 = true := by
  unfold rankKeep
  rw [ms1_length, ms1_rank30]
  decide +kernel
theorem ms1_rank31 : rank2 ms1 (1 / 1) = 249 := by kernel_rfl
theorem ms1_keep31 : rankKeep ms1 (1 / 1) 3 10 = true := by
  unfold rankKeep
  rw [ms1_length, ms1_rank31]
  decide +kernel
theorem ms1_rank32 : rank2 ms1 (7 / 6) = 290 := by kernel_rfl
theorem ms1_keep32 : rankKeep ms1 (7 / 6) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank32]
  decide +kernel
theorem ms1_rank33 : rank2 ms1 (5 / 4) = 292 := by kernel_rfl
theorem ms1_keep33 : rankKeep ms1 (5 / 4) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank33]
  decide +kernel
theorem ms1_rank34 : rank2 ms1 (4 / 3) = 296 := by kernel_rfl
theorem ms1_keep34 : rankKeep ms1 (4 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank34]
  decide +kernel
theorem ms1_rank35 : rank2 ms1 (10 / 7) = 300 := by kernel_rfl
theorem ms1_keep35 : rankKeep ms1 (10 / 7) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank35]
  decide +kernel
theorem ms1_rank36 : rank2 ms1 (3 / 2) = 310 := by kernel_rfl
theorem ms1_keep36 : rankKeep ms1 (3 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank36]
  decide +kernel
theorem ms1_rank37 : rank2 ms1 (5 / 3) = 320 := by kernel_rfl
theorem ms1_keep37 : rankKeep ms1 (5 / 3) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank37]
  decide +kernel
theorem ms1_rank38 : rank2 ms1 (9 / 5) = 322 := by kernel_rfl
theorem ms1_keep38 : rankKeep ms1 (9 / 5) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank38]
  decide +kernel
theorem ms1_rank39 : rank2 ms1 (2 / 1) = 344 := by kernel_rfl
theorem ms1_keep39 : rankKeep ms1 (2 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank39]
  decide +kernel
theorem ms1_rank40 : rank2 ms1 (5 / 2) = 366 := by kernel_rfl
theorem ms1_keep40 : rankKeep ms1 (5 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank40]
  decide +kernel
theorem ms1_rank41 : rank2 ms1 (3 / 1) = 374 := by kernel_rfl
theorem ms1_keep41 : rankKeep ms1 (3 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank41]
  decide +kernel
theorem ms1_rank42 : rank2 ms1 (7 / 2) = 382 := by kernel_rfl
theorem ms1_keep42 : rankKeep ms1 (7 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank42]
  decide +kernel
theorem ms1_rank43 : rank2 ms1 (4 / 1) = 384 := by kernel_rfl
theorem ms1_keep43 : rankKeep ms1 (4 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank43]
  decide +kernel
theorem ms1_rank44 : rank2 ms1 (9 / 2) = 386 := by kernel_rfl
theorem ms1_keep44 : rankKeep ms1 (9 / 2) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank44]
  decide +kernel
theorem ms1_rank45 : rank2 ms1 (5 / 1) = 388 := by kernel_rfl
theorem ms1_keep45 : rankKeep ms1 (5 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank45]
  decide +kernel
theorem ms1_rank46 : rank2 ms1 (11 / 1) = 390 := by kernel_rfl
theorem ms1_keep46 : rankKeep ms1 (11 / 1) 3 10 = false := by
  unfold rankKeep
  rw [ms1_length, ms1_rank46]
  decide +kernel
theorem aa1_length : aa1.length = 195 := by kernel_rfl
theorem aa1_rank0 : rank2 aa1 (1 / 1) = 25 := by kernel_rfl
theorem aa1_keep0 : rankKeep aa1 (1 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank0]
  decide +kernel
theorem aa1_rank1 : rank2 aa1 (2 / 1) = 81 := by kernel_rfl
theorem aa1_keep1 : rankKeep aa1 (2 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank1]
  decide +kernel
theorem aa1_rank2 : rank2 aa1 (3 / 1) = 126 := by kernel_rfl
theorem aa1_keep2 : rankKeep aa1 (3 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank2]
  decide +kernel
theorem aa1_rank3 : rank2 aa1 (4 / 1) = 154 := by kernel_rfl
theorem aa1_keep3 : rankKeep aa1 (4 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank3]
  decide +kernel
theorem aa1_rank4 : rank2 aa1 (5 / 1) = 175 := by kernel_rfl
theorem aa1_keep4 : rankKeep aa1 (5 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank4]
  decide +kernel
theorem aa1_rank5 : rank2 aa1 (6 / 1) = 194 := by kernel_rfl
theorem aa1_keep5 : rankKeep aa1 (6 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank5]
  decide +kernel
theorem aa1_rank6 : rank2 aa1 (8 / 1) = 211 := by kernel_rfl
theorem aa1_keep6 : rankKeep aa1 (8 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank6]
  decide +kernel
theorem aa1_rank7 : rank2 aa1 (9 / 1) = 224 := by kernel_rfl
theorem aa1_keep7 : rankKeep aa1 (9 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank7]
  decide +kernel
theorem aa1_rank8 : rank2 aa1 (10 / 1) = 239 := by kernel_rfl
theorem aa1_keep8 : rankKeep aa1 (10 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank8]
  decide +kernel
theorem aa1_rank9 : rank2 aa1 (11 / 1) = 250 := by kernel_rfl
theorem aa1_keep9 : rankKeep aa1 (11 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank9]
  decide +kernel
theorem aa1_rank10 : rank2 aa1 (12 / 1) = 264 := by kernel_rfl
theorem aa1_keep10 : rankKeep aa1 (12 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank10]
  decide +kernel
theorem aa1_rank11 : rank2 aa1 (14 / 1) = 276 := by kernel_rfl
theorem aa1_keep11 : rankKeep aa1 (14 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank11]
  decide +kernel
theorem aa1_rank12 : rank2 aa1 (15 / 1) = 282 := by kernel_rfl
theorem aa1_keep12 : rankKeep aa1 (15 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank12]
  decide +kernel
theorem aa1_rank13 : rank2 aa1 (16 / 1) = 288 := by kernel_rfl
theorem aa1_keep13 : rankKeep aa1 (16 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank13]
  decide +kernel
theorem aa1_rank14 : rank2 aa1 (18 / 1) = 299 := by kernel_rfl
theorem aa1_keep14 : rankKeep aa1 (18 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank14]
  decide +kernel
theorem aa1_rank15 : rank2 aa1 (20 / 1) = 313 := by kernel_rfl
theorem aa1_keep15 : rankKeep aa1 (20 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank15]
  decide +kernel
theorem aa1_rank16 : rank2 aa1 (24 / 1) = 328 := by kernel_rfl
theorem aa1_keep16 : rankKeep aa1 (24 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank16]
  decide +kernel
theorem aa1_rank17 : rank2 aa1 (26 / 1) = 338 := by kernel_rfl
theorem aa1_keep17 : rankKeep aa1 (26 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank17]
  decide +kernel
theorem aa1_rank18 : rank2 aa1 (27 / 1) = 341 := by kernel_rfl
theorem aa1_keep18 : rankKeep aa1 (27 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank18]
  decide +kernel
theorem aa1_rank19 : rank2 aa1 (28 / 1) = 345 := by kernel_rfl
theorem aa1_keep19 : rankKeep aa1 (28 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank19]
  decide +kernel
theorem aa1_rank20 : rank2 aa1 (30 / 1) = 350 := by kernel_rfl
theorem aa1_keep20 : rankKeep aa1 (30 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank20]
  decide +kernel
theorem aa1_rank21 : rank2 aa1 (36 / 1) = 354 := by kernel_rfl
theorem aa1_keep21 : rankKeep aa1 (36 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank21]
  decide +kernel
theorem aa1_rank22 : rank2 aa1 (38 / 1) = 356 := by kernel_rfl
theorem aa1_keep22 : rankKeep aa1 (38 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank22]
  decide +kernel
theorem aa1_rank23 : rank2 aa1 (39 / 1) = 358 := by kernel_rfl
theorem aa1_keep23 : rankKeep aa1 (39 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank23]
  decide +kernel
theorem aa1_rank24 : rank2 aa1 (40 / 1) = 360 := by kernel_rfl
theorem aa1_keep24 : rankKeep aa1 (40 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank24]
  decide +kernel
theorem aa1_rank25 : rank2 aa1 (42 / 1) = 362 := by kernel_rfl
theorem aa1_keep25 : rankKeep aa1 (42 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank25]
  decide +kernel
theorem aa1_rank26 : rank2 aa1 (44 / 1) = 364 := by kernel_rfl
theorem aa1_keep26 : rankKeep aa1 (44 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank26]
  decide +kernel
theorem aa1_rank27 : rank2 aa1 (45 / 1) = 366 := by kernel_rfl
theorem aa1_keep27 : rankKeep aa1 (45 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank27]
  decide +kernel
theorem aa1_rank28 : rank2 aa1 (46 / 1) = 368 := by kernel_rfl
theorem aa1_keep28 : rankKeep aa1 (46 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank28]
  decide +kernel
theorem aa1_rank29 : rank2 aa1 (63 / 1) = 371 := by kernel_rfl
theorem aa1_keep29 : rankKeep aa1 (63 / 1) 1 20 = true := by
  unfold rankKeep
  rw [aa1_length, aa1_rank29]
  decide +kernel
theorem aa1_rank30 : rank2 aa1 (68 / 1) = 374 := by kernel_rfl
theorem aa1_keep30 : rankKeep aa1 (68 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa1_length, aa1_rank30]
  decide +kernel
theorem aa1_rank31 : rank2 aa1 (70 / 1) = 377 := by kernel_rfl
theorem aa1_keep31 : rankKeep aa1 (70 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa1_length, aa1_rank31]
  decide +kernel
theorem aa1_rank32 : rank2 aa1 (80 / 1) = 381 := by kernel_rfl
theorem aa1_keep32 : rankKeep aa1 (80 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa1_length, aa1_rank32]
  decide +kernel
theorem aa1_rank33 : rank2 aa1 (100 / 1) = 384 := by kernel_rfl
theorem aa1_keep33 : rankKeep aa1 (100 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa1_length, aa1_rank33]
  decide +kernel
theorem aa1_rank34 : rank2 aa1 (174 / 1) = 386 := by kernel_rfl
theorem aa1_keep34 : rankKeep aa1 (174 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa1_length, aa1_rank34]
  decide +kernel
theorem aa1_rank35 : rank2 aa1 (176 / 1) = 388 := by kernel_rfl
theorem aa1_keep35 : rankKeep aa1 (176 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa1_length, aa1_rank35]
  decide +kernel
theorem aa1_rank36 : rank2 aa1 (450 / 1) = 390 := by kernel_rfl
theorem aa1_keep36 : rankKeep aa1 (450 / 1) 1 20 = false := by
  unfold rankKeep
  rw [aa1_length, aa1_rank36]
  decide +kernel
end Proofs.Witness
