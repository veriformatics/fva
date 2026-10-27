import Proofs.Bounds
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Proofs.Numeric
def lb (n : Nat) : ℚ :=
  match n with
  | 0 => 0 / 1000000000
  | 1 => 0 / 1000000000
  | 2 => 693147180 / 1000000000
  | 3 => 1098612288 / 1000000000
  | 4 => 1386294361 / 1000000000
  | 5 => 1609437912 / 1000000000
  | 6 => 1791759469 / 1000000000
  | 7 => 1945910149 / 1000000000
  | 8 => 2079441541 / 1000000000
  | 9 => 2197224577 / 1000000000
  | 10 => 2302585092 / 1000000000
  | 11 => 2397895272 / 1000000000
  | 12 => 2484906649 / 1000000000
  | 13 => 2564949357 / 1000000000
  | 14 => 2639057329 / 1000000000
  | 15 => 2708050201 / 1000000000
  | 16 => 2772588722 / 1000000000
  | 17 => 2833213344 / 1000000000
  | 18 => 2890371757 / 1000000000
  | 19 => 2944438979 / 1000000000
  | 20 => 2995732273 / 1000000000
  | 21 => 3044522437 / 1000000000
  | 22 => 3091042453 / 1000000000
  | 23 => 3135494215 / 1000000000
  | 24 => 3178053830 / 1000000000
  | 25 => 3218875824 / 1000000000
  | 26 => 3258096538 / 1000000000
  | 27 => 3295836866 / 1000000000
  | 28 => 3332204510 / 1000000000
  | 29 => 3367295829 / 1000000000
  | 30 => 3401197381 / 1000000000
  | 31 => 3433987204 / 1000000000
  | 32 => 3465735902 / 1000000000
  | 33 => 3496507561 / 1000000000
  | 34 => 3526360524 / 1000000000
  | 35 => 3555348061 / 1000000000
  | 36 => 3583518938 / 1000000000
  | 37 => 3610917912 / 1000000000
  | 38 => 3637586159 / 1000000000
  | 39 => 3663561646 / 1000000000
  | 40 => 3688879454 / 1000000000
  | 41 => 3713572066 / 1000000000
  | 42 => 3737669618 / 1000000000
  | 621 => 6431331081 / 1000000000
  | 755 => 6626717749 / 1000000000
  | 1097 => 7000334460 / 1000000000
  | 1136 => 7035268599 / 1000000000
  | 1219 => 7105786129 / 1000000000
  | 1261 => 7139660335 / 1000000000
  | 1916 => 7557994958 / 1000000000
  | _ => 0
def ub (n : Nat) : ℚ :=
  match n with
  | 0 => 0 / 1000000000
  | 1 => 0 / 1000000000
  | 2 => 693147181 / 1000000000
  | 3 => 1098612289 / 1000000000
  | 4 => 1386294362 / 1000000000
  | 5 => 1609437913 / 1000000000
  | 6 => 1791759470 / 1000000000
  | 7 => 1945910150 / 1000000000
  | 8 => 2079441542 / 1000000000
  | 9 => 2197224578 / 1000000000
  | 10 => 2302585093 / 1000000000
  | 11 => 2397895273 / 1000000000
  | 12 => 2484906650 / 1000000000
  | 13 => 2564949358 / 1000000000
  | 14 => 2639057330 / 1000000000
  | 15 => 2708050202 / 1000000000
  | 16 => 2772588723 / 1000000000
  | 17 => 2833213345 / 1000000000
  | 18 => 2890371758 / 1000000000
  | 19 => 2944438980 / 1000000000
  | 20 => 2995732274 / 1000000000
  | 21 => 3044522438 / 1000000000
  | 22 => 3091042454 / 1000000000
  | 23 => 3135494216 / 1000000000
  | 24 => 3178053831 / 1000000000
  | 25 => 3218875825 / 1000000000
  | 26 => 3258096539 / 1000000000
  | 27 => 3295836867 / 1000000000
  | 28 => 3332204511 / 1000000000
  | 29 => 3367295830 / 1000000000
  | 30 => 3401197382 / 1000000000
  | 31 => 3433987205 / 1000000000
  | 32 => 3465735903 / 1000000000
  | 33 => 3496507562 / 1000000000
  | 34 => 3526360525 / 1000000000
  | 35 => 3555348062 / 1000000000
  | 36 => 3583518939 / 1000000000
  | 37 => 3610917913 / 1000000000
  | 38 => 3637586160 / 1000000000
  | 39 => 3663561647 / 1000000000
  | 40 => 3688879455 / 1000000000
  | 41 => 3713572067 / 1000000000
  | 42 => 3737669619 / 1000000000
  | 621 => 6431331082 / 1000000000
  | 755 => 6626717750 / 1000000000
  | 1097 => 7000334461 / 1000000000
  | 1136 => 7035268600 / 1000000000
  | 1219 => 7105786130 / 1000000000
  | 1261 => 7139660336 / 1000000000
  | 1916 => 7557994959 / 1000000000
  | _ => n
theorem log0 : (lb 0 : ℝ) ≤ Real.log 0 ∧ Real.log 0 ≤ (ub 0 : ℝ) := by
  norm_num [lb, ub]
theorem log1 : (lb 1 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ (ub 1 : ℝ) := by
  norm_num [lb, ub]
theorem log2 : (lb 2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (ub 2 : ℝ) := by
  exact log_certificate 2 1 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log3 : (lb 3 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ (ub 3 : ℝ) := by
  exact log_certificate 3 1 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log4 : (lb 4 : ℝ) ≤ Real.log 4 ∧ Real.log 4 ≤ (ub 4 : ℝ) := by
  exact log_certificate 4 2 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log5 : (lb 5 : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ (ub 5 : ℝ) := by
  exact log_certificate 5 2 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log6 : (lb 6 : ℝ) ≤ Real.log 6 ∧ Real.log 6 ≤ (ub 6 : ℝ) := by
  exact log_certificate 6 2 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log7 : (lb 7 : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ (ub 7 : ℝ) := by
  exact log_certificate 7 2 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log8 : (lb 8 : ℝ) ≤ Real.log 8 ∧ Real.log 8 ≤ (ub 8 : ℝ) := by
  exact log_certificate 8 3 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log9 : (lb 9 : ℝ) ≤ Real.log 9 ∧ Real.log 9 ≤ (ub 9 : ℝ) := by
  exact log_certificate 9 3 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log10 : (lb 10 : ℝ) ≤ Real.log 10 ∧ Real.log 10 ≤ (ub 10 : ℝ) := by
  exact log_certificate 10 3 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log11 : (lb 11 : ℝ) ≤ Real.log 11 ∧ Real.log 11 ≤ (ub 11 : ℝ) := by
  exact log_certificate 11 3 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log12 : (lb 12 : ℝ) ≤ Real.log 12 ∧ Real.log 12 ≤ (ub 12 : ℝ) := by
  exact log_certificate 12 3 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log13 : (lb 13 : ℝ) ≤ Real.log 13 ∧ Real.log 13 ≤ (ub 13 : ℝ) := by
  exact log_certificate 13 3 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log14 : (lb 14 : ℝ) ≤ Real.log 14 ∧ Real.log 14 ≤ (ub 14 : ℝ) := by
  exact log_certificate 14 3 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log15 : (lb 15 : ℝ) ≤ Real.log 15 ∧ Real.log 15 ≤ (ub 15 : ℝ) := by
  exact log_certificate 15 3 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log16 : (lb 16 : ℝ) ≤ Real.log 16 ∧ Real.log 16 ≤ (ub 16 : ℝ) := by
  exact log_certificate 16 4 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log17 : (lb 17 : ℝ) ≤ Real.log 17 ∧ Real.log 17 ≤ (ub 17 : ℝ) := by
  exact log_certificate 17 4 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log18 : (lb 18 : ℝ) ≤ Real.log 18 ∧ Real.log 18 ≤ (ub 18 : ℝ) := by
  exact log_certificate 18 4 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log19 : (lb 19 : ℝ) ≤ Real.log 19 ∧ Real.log 19 ≤ (ub 19 : ℝ) := by
  exact log_certificate 19 4 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log20 : (lb 20 : ℝ) ≤ Real.log 20 ∧ Real.log 20 ≤ (ub 20 : ℝ) := by
  exact log_certificate 20 4 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log21 : (lb 21 : ℝ) ≤ Real.log 21 ∧ Real.log 21 ≤ (ub 21 : ℝ) := by
  exact log_certificate 21 4 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log22 : (lb 22 : ℝ) ≤ Real.log 22 ∧ Real.log 22 ≤ (ub 22 : ℝ) := by
  exact log_certificate 22 4 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log23 : (lb 23 : ℝ) ≤ Real.log 23 ∧ Real.log 23 ≤ (ub 23 : ℝ) := by
  exact log_certificate 23 4 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log24 : (lb 24 : ℝ) ≤ Real.log 24 ∧ Real.log 24 ≤ (ub 24 : ℝ) := by
  exact log_certificate 24 4 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log25 : (lb 25 : ℝ) ≤ Real.log 25 ∧ Real.log 25 ≤ (ub 25 : ℝ) := by
  exact log_certificate 25 4 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log26 : (lb 26 : ℝ) ≤ Real.log 26 ∧ Real.log 26 ≤ (ub 26 : ℝ) := by
  exact log_certificate 26 4 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log27 : (lb 27 : ℝ) ≤ Real.log 27 ∧ Real.log 27 ≤ (ub 27 : ℝ) := by
  exact log_certificate 27 4 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log28 : (lb 28 : ℝ) ≤ Real.log 28 ∧ Real.log 28 ≤ (ub 28 : ℝ) := by
  exact log_certificate 28 4 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log29 : (lb 29 : ℝ) ≤ Real.log 29 ∧ Real.log 29 ≤ (ub 29 : ℝ) := by
  exact log_certificate 29 4 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log30 : (lb 30 : ℝ) ≤ Real.log 30 ∧ Real.log 30 ≤ (ub 30 : ℝ) := by
  exact log_certificate 30 4 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log31 : (lb 31 : ℝ) ≤ Real.log 31 ∧ Real.log 31 ≤ (ub 31 : ℝ) := by
  exact log_certificate 31 4 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log32 : (lb 32 : ℝ) ≤ Real.log 32 ∧ Real.log 32 ≤ (ub 32 : ℝ) := by
  exact log_certificate 32 5 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log33 : (lb 33 : ℝ) ≤ Real.log 33 ∧ Real.log 33 ≤ (ub 33 : ℝ) := by
  exact log_certificate 33 5 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log34 : (lb 34 : ℝ) ≤ Real.log 34 ∧ Real.log 34 ≤ (ub 34 : ℝ) := by
  exact log_certificate 34 5 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log35 : (lb 35 : ℝ) ≤ Real.log 35 ∧ Real.log 35 ≤ (ub 35 : ℝ) := by
  exact log_certificate 35 5 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log36 : (lb 36 : ℝ) ≤ Real.log 36 ∧ Real.log 36 ≤ (ub 36 : ℝ) := by
  exact log_certificate 36 5 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log37 : (lb 37 : ℝ) ≤ Real.log 37 ∧ Real.log 37 ≤ (ub 37 : ℝ) := by
  exact log_certificate 37 5 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log38 : (lb 38 : ℝ) ≤ Real.log 38 ∧ Real.log 38 ≤ (ub 38 : ℝ) := by
  exact log_certificate 38 5 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log39 : (lb 39 : ℝ) ≤ Real.log 39 ∧ Real.log 39 ≤ (ub 39 : ℝ) := by
  exact log_certificate 39 5 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log40 : (lb 40 : ℝ) ≤ Real.log 40 ∧ Real.log 40 ≤ (ub 40 : ℝ) := by
  exact log_certificate 40 5 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log41 : (lb 41 : ℝ) ≤ Real.log 41 ∧ Real.log 41 ≤ (ub 41 : ℝ) := by
  exact log_certificate 41 5 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log42 : (lb 42 : ℝ) ≤ Real.log 42 ∧ Real.log 42 ≤ (ub 42 : ℝ) := by
  exact log_certificate 42 5 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log621 : (lb 621 : ℝ) ≤ Real.log 621 ∧ Real.log 621 ≤ (ub 621 : ℝ) := by
  exact log_certificate 621 9 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log755 : (lb 755 : ℝ) ≤ Real.log 755 ∧ Real.log 755 ≤ (ub 755 : ℝ) := by
  exact log_certificate 755 9 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log1097 : (lb 1097 : ℝ) ≤ Real.log 1097 ∧ Real.log 1097 ≤ (ub 1097 : ℝ) := by
  exact log_certificate 1097 10 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log1136 : (lb 1136 : ℝ) ≤ Real.log 1136 ∧ Real.log 1136 ≤ (ub 1136 : ℝ) := by
  exact log_certificate 1136 10 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log1219 : (lb 1219 : ℝ) ≤ Real.log 1219 ∧ Real.log 1219 ≤ (ub 1219 : ℝ) := by
  exact log_certificate 1219 10 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log1261 : (lb 1261 : ℝ) ≤ Real.log 1261 ∧ Real.log 1261 ≤ (ub 1261 : ℝ) := by
  exact log_certificate 1261 10 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log1916 : (lb 1916 : ℝ) ≤ Real.log 1916 ∧ Real.log 1916 ≤ (ub 1916 : ℝ) := by
  exact log_certificate 1916 10 _ _ (by norm_num) (by decide +kernel) (by decide +kernel)
theorem log_bounds (n : Nat) : (lb n : ℝ) ≤ Real.log n ∧ Real.log n ≤ (ub n : ℝ) := by
  by_cases h : n ≤ 42
  · interval_cases n
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log0
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log1
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log2
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log3
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log4
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log5
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log6
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log7
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log8
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log9
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log10
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log11
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log12
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log13
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log14
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log15
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log16
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log17
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log18
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log19
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log20
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log21
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log22
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log23
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log24
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log25
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log26
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log27
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log28
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log29
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log30
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log31
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log32
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log33
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log34
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log35
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log36
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log37
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log38
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log39
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log40
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log41
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log42
  by_cases h621 : n = 621
  · subst n; exact log621
  by_cases h755 : n = 755
  · subst n; exact log755
  by_cases h1097 : n = 1097
  · subst n; exact log1097
  by_cases h1136 : n = 1136
  · subst n; exact log1136
  by_cases h1219 : n = 1219
  · subst n; exact log1219
  by_cases h1261 : n = 1261
  · subst n; exact log1261
  by_cases h1916 : n = 1916
  · subst n; exact log1916
  have hlo : lb n = 0 := by unfold lb; split <;> first | rfl | omega
  have hhi : ub n = n := by unfold ub; split <;> first | rfl | omega
  rw [hlo, hhi]
  exact ⟨by simpa using Real.log_natCast_nonneg n, by exact_mod_cast Real.log_le_self (Nat.cast_nonneg n)⟩

end Proofs.Numeric
