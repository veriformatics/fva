import Proofs.Bounds

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Proofs

theorem ln1 : ((-1 : ℚ)/1000000 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ ((1 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 1 0 (1/1) (-1/1000000) (1/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln2 : ((693146 : ℚ)/1000000 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((693149 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 2 1 (1/1) (693146/1000000) (693149/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln3 : ((1098611 : ℚ)/1000000 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((1098614 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 3 1 (3/2) (1098611/1000000) (1098614/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln4 : ((1386293 : ℚ)/1000000 : ℝ) ≤ Real.log 4 ∧ Real.log 4 ≤ ((1386296 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 4 2 (1/1) (1386293/1000000) (1386296/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln5 : ((1609436 : ℚ)/1000000 : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((1609439 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 5 2 (5/4) (1609436/1000000) (1609439/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln6 : ((1791758 : ℚ)/1000000 : ℝ) ≤ Real.log 6 ∧ Real.log 6 ≤ ((1791761 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 6 2 (3/2) (1791758/1000000) (1791761/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln7 : ((1945909 : ℚ)/1000000 : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((1945912 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 7 2 (7/4) (1945909/1000000) (1945912/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln8 : ((2079440 : ℚ)/1000000 : ℝ) ≤ Real.log 8 ∧ Real.log 8 ≤ ((2079443 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 8 3 (1/1) (2079440/1000000) (2079443/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln9 : ((2197223 : ℚ)/1000000 : ℝ) ≤ Real.log 9 ∧ Real.log 9 ≤ ((2197226 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 9 3 (9/8) (2197223/1000000) (2197226/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln10 : ((2302584 : ℚ)/1000000 : ℝ) ≤ Real.log 10 ∧ Real.log 10 ≤ ((2302587 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 10 3 (5/4) (2302584/1000000) (2302587/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln11 : ((2397894 : ℚ)/1000000 : ℝ) ≤ Real.log 11 ∧ Real.log 11 ≤ ((2397897 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 11 3 (11/8) (2397894/1000000) (2397897/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln12 : ((2484905 : ℚ)/1000000 : ℝ) ≤ Real.log 12 ∧ Real.log 12 ≤ ((2484908 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 12 3 (3/2) (2484905/1000000) (2484908/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln13 : ((2564948 : ℚ)/1000000 : ℝ) ≤ Real.log 13 ∧ Real.log 13 ≤ ((2564951 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 13 3 (13/8) (2564948/1000000) (2564951/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln14 : ((2639056 : ℚ)/1000000 : ℝ) ≤ Real.log 14 ∧ Real.log 14 ≤ ((2639059 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 14 3 (7/4) (2639056/1000000) (2639059/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln15 : ((2708049 : ℚ)/1000000 : ℝ) ≤ Real.log 15 ∧ Real.log 15 ≤ ((2708052 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 15 3 (15/8) (2708049/1000000) (2708052/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln16 : ((2772587 : ℚ)/1000000 : ℝ) ≤ Real.log 16 ∧ Real.log 16 ≤ ((2772590 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 16 4 (1/1) (2772587/1000000) (2772590/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln17 : ((2833212 : ℚ)/1000000 : ℝ) ≤ Real.log 17 ∧ Real.log 17 ≤ ((2833215 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 17 4 (17/16) (2833212/1000000) (2833215/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln18 : ((2890370 : ℚ)/1000000 : ℝ) ≤ Real.log 18 ∧ Real.log 18 ≤ ((2890373 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 18 4 (9/8) (2890370/1000000) (2890373/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln19 : ((2944437 : ℚ)/1000000 : ℝ) ≤ Real.log 19 ∧ Real.log 19 ≤ ((2944440 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 19 4 (19/16) (2944437/1000000) (2944440/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln20 : ((2995731 : ℚ)/1000000 : ℝ) ≤ Real.log 20 ∧ Real.log 20 ≤ ((2995734 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 20 4 (5/4) (2995731/1000000) (2995734/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln21 : ((3044521 : ℚ)/1000000 : ℝ) ≤ Real.log 21 ∧ Real.log 21 ≤ ((3044524 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 21 4 (21/16) (3044521/1000000) (3044524/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln22 : ((3091041 : ℚ)/1000000 : ℝ) ≤ Real.log 22 ∧ Real.log 22 ≤ ((3091044 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 22 4 (11/8) (3091041/1000000) (3091044/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln23 : ((3135493 : ℚ)/1000000 : ℝ) ≤ Real.log 23 ∧ Real.log 23 ≤ ((3135496 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 23 4 (23/16) (3135493/1000000) (3135496/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln24 : ((3178052 : ℚ)/1000000 : ℝ) ≤ Real.log 24 ∧ Real.log 24 ≤ ((3178055 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 24 4 (3/2) (3178052/1000000) (3178055/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln25 : ((3218874 : ℚ)/1000000 : ℝ) ≤ Real.log 25 ∧ Real.log 25 ≤ ((3218877 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 25 4 (25/16) (3218874/1000000) (3218877/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln26 : ((3258095 : ℚ)/1000000 : ℝ) ≤ Real.log 26 ∧ Real.log 26 ≤ ((3258098 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 26 4 (13/8) (3258095/1000000) (3258098/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln27 : ((3295835 : ℚ)/1000000 : ℝ) ≤ Real.log 27 ∧ Real.log 27 ≤ ((3295838 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 27 4 (27/16) (3295835/1000000) (3295838/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln28 : ((3332203 : ℚ)/1000000 : ℝ) ≤ Real.log 28 ∧ Real.log 28 ≤ ((3332206 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 28 4 (7/4) (3332203/1000000) (3332206/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln29 : ((3367294 : ℚ)/1000000 : ℝ) ≤ Real.log 29 ∧ Real.log 29 ≤ ((3367297 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 29 4 (29/16) (3367294/1000000) (3367297/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln30 : ((3401196 : ℚ)/1000000 : ℝ) ≤ Real.log 30 ∧ Real.log 30 ≤ ((3401199 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 30 4 (15/8) (3401196/1000000) (3401199/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln31 : ((3433986 : ℚ)/1000000 : ℝ) ≤ Real.log 31 ∧ Real.log 31 ≤ ((3433989 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 31 4 (31/16) (3433986/1000000) (3433989/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln32 : ((3465734 : ℚ)/1000000 : ℝ) ≤ Real.log 32 ∧ Real.log 32 ≤ ((3465737 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 32 5 (1/1) (3465734/1000000) (3465737/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln33 : ((3496506 : ℚ)/1000000 : ℝ) ≤ Real.log 33 ∧ Real.log 33 ≤ ((3496509 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 33 5 (33/32) (3496506/1000000) (3496509/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln34 : ((3526359 : ℚ)/1000000 : ℝ) ≤ Real.log 34 ∧ Real.log 34 ≤ ((3526362 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 34 5 (17/16) (3526359/1000000) (3526362/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln35 : ((3555347 : ℚ)/1000000 : ℝ) ≤ Real.log 35 ∧ Real.log 35 ≤ ((3555350 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 35 5 (35/32) (3555347/1000000) (3555350/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln36 : ((3583517 : ℚ)/1000000 : ℝ) ≤ Real.log 36 ∧ Real.log 36 ≤ ((3583520 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 36 5 (9/8) (3583517/1000000) (3583520/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln37 : ((3610916 : ℚ)/1000000 : ℝ) ≤ Real.log 37 ∧ Real.log 37 ≤ ((3610919 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 37 5 (37/32) (3610916/1000000) (3610919/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln38 : ((3637585 : ℚ)/1000000 : ℝ) ≤ Real.log 38 ∧ Real.log 38 ≤ ((3637588 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 38 5 (19/16) (3637585/1000000) (3637588/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln39 : ((3663560 : ℚ)/1000000 : ℝ) ≤ Real.log 39 ∧ Real.log 39 ≤ ((3663563 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 39 5 (39/32) (3663560/1000000) (3663563/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln40 : ((3688878 : ℚ)/1000000 : ℝ) ≤ Real.log 40 ∧ Real.log 40 ≤ ((3688881 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 40 5 (5/4) (3688878/1000000) (3688881/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln41 : ((3713571 : ℚ)/1000000 : ℝ) ≤ Real.log 41 ∧ Real.log 41 ≤ ((3713574 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 41 5 (41/32) (3713571/1000000) (3713574/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln42 : ((3737668 : ℚ)/1000000 : ℝ) ≤ Real.log 42 ∧ Real.log 42 ≤ ((3737671 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 42 5 (21/16) (3737668/1000000) (3737671/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln621 : ((6431330 : ℚ)/1000000 : ℝ) ≤ Real.log 621 ∧ Real.log 621 ≤ ((6431333 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 621 9 (621/512) (6431330/1000000) (6431333/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln755 : ((6626716 : ℚ)/1000000 : ℝ) ≤ Real.log 755 ∧ Real.log 755 ≤ ((6626719 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 755 9 (755/512) (6626716/1000000) (6626719/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln1097 : ((7000333 : ℚ)/1000000 : ℝ) ≤ Real.log 1097 ∧ Real.log 1097 ≤ ((7000336 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 1097 10 (1097/1024) (7000333/1000000) (7000336/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln1136 : ((7035267 : ℚ)/1000000 : ℝ) ≤ Real.log 1136 ∧ Real.log 1136 ≤ ((7035270 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 1136 10 (71/64) (7035267/1000000) (7035270/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln1219 : ((7105785 : ℚ)/1000000 : ℝ) ≤ Real.log 1219 ∧ Real.log 1219 ≤ ((7105788 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 1219 10 (1219/1024) (7105785/1000000) (7105788/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln1261 : ((7139659 : ℚ)/1000000 : ℝ) ≤ Real.log 1261 ∧ Real.log 1261 ≤ ((7139662 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 1261 10 (1261/1024) (7139659/1000000) (7139662/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

theorem ln1916 : ((7557993 : ℚ)/1000000 : ℝ) ≤ Real.log 1916 ∧ Real.log 1916 ≤ ((7557996 : ℚ)/1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using
    (log_certificate 1916 10 (479/256) (7557993/1000000) (7557996/1000000)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))

def logLo (n : Nat) : ℚ :=
  match n with
  | 1 => -1/1000000
  | 2 => 693146/1000000
  | 3 => 1098611/1000000
  | 4 => 1386293/1000000
  | 5 => 1609436/1000000
  | 6 => 1791758/1000000
  | 7 => 1945909/1000000
  | 8 => 2079440/1000000
  | 9 => 2197223/1000000
  | 10 => 2302584/1000000
  | 11 => 2397894/1000000
  | 12 => 2484905/1000000
  | 13 => 2564948/1000000
  | 14 => 2639056/1000000
  | 15 => 2708049/1000000
  | 16 => 2772587/1000000
  | 17 => 2833212/1000000
  | 18 => 2890370/1000000
  | 19 => 2944437/1000000
  | 20 => 2995731/1000000
  | 21 => 3044521/1000000
  | 22 => 3091041/1000000
  | 23 => 3135493/1000000
  | 24 => 3178052/1000000
  | 25 => 3218874/1000000
  | 26 => 3258095/1000000
  | 27 => 3295835/1000000
  | 28 => 3332203/1000000
  | 29 => 3367294/1000000
  | 30 => 3401196/1000000
  | 31 => 3433986/1000000
  | 32 => 3465734/1000000
  | 33 => 3496506/1000000
  | 34 => 3526359/1000000
  | 35 => 3555347/1000000
  | 36 => 3583517/1000000
  | 37 => 3610916/1000000
  | 38 => 3637585/1000000
  | 39 => 3663560/1000000
  | 40 => 3688878/1000000
  | 41 => 3713571/1000000
  | 42 => 3737668/1000000
  | 621 => 6431330/1000000
  | 755 => 6626716/1000000
  | 1097 => 7000333/1000000
  | 1136 => 7035267/1000000
  | 1219 => 7105785/1000000
  | 1261 => 7139659/1000000
  | 1916 => 7557993/1000000
  | _ => 0

def logHi (n : Nat) : ℚ :=
  match n with
  | 1 => 1/1000000
  | 2 => 693149/1000000
  | 3 => 1098614/1000000
  | 4 => 1386296/1000000
  | 5 => 1609439/1000000
  | 6 => 1791761/1000000
  | 7 => 1945912/1000000
  | 8 => 2079443/1000000
  | 9 => 2197226/1000000
  | 10 => 2302587/1000000
  | 11 => 2397897/1000000
  | 12 => 2484908/1000000
  | 13 => 2564951/1000000
  | 14 => 2639059/1000000
  | 15 => 2708052/1000000
  | 16 => 2772590/1000000
  | 17 => 2833215/1000000
  | 18 => 2890373/1000000
  | 19 => 2944440/1000000
  | 20 => 2995734/1000000
  | 21 => 3044524/1000000
  | 22 => 3091044/1000000
  | 23 => 3135496/1000000
  | 24 => 3178055/1000000
  | 25 => 3218877/1000000
  | 26 => 3258098/1000000
  | 27 => 3295838/1000000
  | 28 => 3332206/1000000
  | 29 => 3367297/1000000
  | 30 => 3401199/1000000
  | 31 => 3433989/1000000
  | 32 => 3465737/1000000
  | 33 => 3496509/1000000
  | 34 => 3526362/1000000
  | 35 => 3555350/1000000
  | 36 => 3583520/1000000
  | 37 => 3610919/1000000
  | 38 => 3637588/1000000
  | 39 => 3663563/1000000
  | 40 => 3688881/1000000
  | 41 => 3713574/1000000
  | 42 => 3737671/1000000
  | 621 => 6431333/1000000
  | 755 => 6626719/1000000
  | 1097 => 7000336/1000000
  | 1136 => 7035270/1000000
  | 1219 => 7105788/1000000
  | 1261 => 7139662/1000000
  | 1916 => 7557996/1000000
  | _ => 0

def logDomain : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 621, 755, 1097, 1136, 1219, 1261, 1916]

theorem log_bounds (n : Nat) (hn : n ∈ logDomain) :
    (logLo n : ℝ) ≤ Real.log n ∧ Real.log n ≤ (logHi n : ℝ) := by
  simp only [logDomain, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [logLo, logHi] using ln1
  · simpa [logLo, logHi] using ln2
  · simpa [logLo, logHi] using ln3
  · simpa [logLo, logHi] using ln4
  · simpa [logLo, logHi] using ln5
  · simpa [logLo, logHi] using ln6
  · simpa [logLo, logHi] using ln7
  · simpa [logLo, logHi] using ln8
  · simpa [logLo, logHi] using ln9
  · simpa [logLo, logHi] using ln10
  · simpa [logLo, logHi] using ln11
  · simpa [logLo, logHi] using ln12
  · simpa [logLo, logHi] using ln13
  · simpa [logLo, logHi] using ln14
  · simpa [logLo, logHi] using ln15
  · simpa [logLo, logHi] using ln16
  · simpa [logLo, logHi] using ln17
  · simpa [logLo, logHi] using ln18
  · simpa [logLo, logHi] using ln19
  · simpa [logLo, logHi] using ln20
  · simpa [logLo, logHi] using ln21
  · simpa [logLo, logHi] using ln22
  · simpa [logLo, logHi] using ln23
  · simpa [logLo, logHi] using ln24
  · simpa [logLo, logHi] using ln25
  · simpa [logLo, logHi] using ln26
  · simpa [logLo, logHi] using ln27
  · simpa [logLo, logHi] using ln28
  · simpa [logLo, logHi] using ln29
  · simpa [logLo, logHi] using ln30
  · simpa [logLo, logHi] using ln31
  · simpa [logLo, logHi] using ln32
  · simpa [logLo, logHi] using ln33
  · simpa [logLo, logHi] using ln34
  · simpa [logLo, logHi] using ln35
  · simpa [logLo, logHi] using ln36
  · simpa [logLo, logHi] using ln37
  · simpa [logLo, logHi] using ln38
  · simpa [logLo, logHi] using ln39
  · simpa [logLo, logHi] using ln40
  · simpa [logLo, logHi] using ln41
  · simpa [logLo, logHi] using ln42
  · simpa [logLo, logHi] using ln621
  · simpa [logLo, logHi] using ln755
  · simpa [logLo, logHi] using ln1097
  · simpa [logLo, logHi] using ln1136
  · simpa [logLo, logHi] using ln1219
  · simpa [logLo, logHi] using ln1261
  · simpa [logLo, logHi] using ln1916

end Proofs
