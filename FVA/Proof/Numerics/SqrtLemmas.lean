import FVA.Proof.Numerics.Basic

/-!
# Fine-grid rounding brackets

A binade's rounding boundaries lie on the half-ulp grid. An open cell of a finer dyadic grid
contains no boundary, so every point in the cell rounds identically.
-/

namespace FVA.Wasm.Num

open FVal Impl

lemma rneNat_half_interval {j : ℕ} {x : ℝ}
    (hl : (j : ℝ) / 2 < x) (hu : x < ((j : ℝ) + 1) / 2) :
    rneNat x = (j + 1) / 2 := by
  have hmod := Nat.mod_lt j (by decide : 0 < 2)
  have hdiv : (j : ℝ) = 2 * (j / 2 : ℕ) + (j % 2 : ℕ) := by
    exact_mod_cast (Nat.div_add_mod j 2).symm
  have hlo : ((j / 2 : ℕ) : ℝ) < x := by
    have : (0 : ℝ) ≤ (j % 2 : ℕ) := Nat.cast_nonneg _
    linarith
  have hhi : x < (j / 2 : ℕ) + 1 := by
    have : ((j % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (show j % 2 ≤ 1 by omega)
    linarith
  unfold rneNat
  rw [roundEven_toNat_between hlo hhi]
  rcases (show j % 2 = 0 ∨ j % 2 = 1 by omega) with he | he
  · have hhalf : x - (j / 2 : ℕ) < 1 / 2 := by rw [he, Nat.cast_zero] at hdiv; linarith
    simp only [hhalf, ↓reduceIte]
    omega
  · have hhalf : x - (j / 2 : ℕ) > 1 / 2 := by rw [he, Nat.cast_one] at hdiv; linarith
    simp only [not_lt_of_ge hhalf.le, hhalf, ↓reduceIte]
    omega

lemma rneNat_fine_interval {r c : ℕ} {x : ℝ} (hc : 0 < c)
    (hl : (r : ℝ) / (2 * c) < x) (hu : x < ((r : ℝ) + 1) / (2 * c)) :
    rneNat x = (r / c + 1) / 2 := by
  apply rneNat_half_interval
  · have hrc : ((r / c : ℕ) : ℝ) * c ≤ r := by
      exact_mod_cast Nat.div_mul_le_self r c
    have hcR : (0 : ℝ) < c := by exact_mod_cast hc
    have hlo : ((r / c : ℕ) : ℝ) / 2 ≤ (r : ℝ) / (2 * c) := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by positivity)]
      nlinarith
    exact lt_of_le_of_lt hlo hl
  · have hrc : (r : ℝ) + 1 ≤ ((r / c : ℕ) + 1) * c := by
      have h := Nat.mod_lt r hc
      have hd := Nat.div_add_mod r c
      have hh : r + 1 ≤ (r / c + 1) * c := by nlinarith
      exact_mod_cast hh
    have hcR : (0 : ℝ) < c := by exact_mod_cast hc
    have hhi : ((r : ℝ) + 1) / (2 * c) ≤ ((r / c : ℕ) + 1) / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    exact lt_of_lt_of_le hu hhi

lemma binade_fine_interval {r : ℕ} {u : ℤ} {x : ℝ} (hr : 0 < r)
    (hl : (r : ℝ) * 2 ^ u < x) (hu : x < ((r : ℝ) + 1) * 2 ^ u) :
    binade x = (Nat.log2 r : ℤ) + u := by
  have hp : 0 < x := lt_trans (mul_pos (by exact_mod_cast hr) (two_zpow_pos u)) hl
  unfold binade
  rw [abs_of_pos hp]
  apply int_log_two_eq hp
  · rw [zpow_add₀ two_ne_zero, zpow_natCast]
    have h : (2 : ℝ) ^ Nat.log2 r ≤ r := by
      exact_mod_cast Nat.log2_self_le (by omega : r ≠ 0)
    exact le_trans (mul_le_mul_of_nonneg_right h (two_zpow_pos u).le) hl.le
  · rw [show (Nat.log2 r : ℤ) + u + 1 = ((Nat.log2 r + 1 : ℕ) : ℤ) + u by
      push_cast; ring, zpow_add₀ two_ne_zero, zpow_natCast]
    have h : (r : ℝ) + 1 ≤ 2 ^ (Nat.log2 r + 1) := by
      exact_mod_cast (show r + 1 ≤ 2 ^ (Nat.log2 r + 1) from Nat.lt_log2_self)
    exact lt_of_lt_of_le hu (mul_le_mul_of_nonneg_right h (two_zpow_pos u).le)

lemma gridRound_fine_interval {F : FloatFormat} {r : ℕ} {u : ℤ} {x y : ℝ}
    (hr : 2 ^ (F.M + 1) ≤ r)
    (hx₁ : (r : ℝ) * 2 ^ u < x) (hx₂ : x < ((r : ℝ) + 1) * 2 ^ u)
    (hy₁ : (r : ℝ) * 2 ^ u < y) (hy₂ : y < ((r : ℝ) + 1) * 2 ^ u) :
    gridRound F x = gridRound F y := by
  have hr0 : 0 < r := lt_of_lt_of_le (Nat.two_pow_pos _) hr
  have hx0 : 0 < x := lt_trans (mul_pos (by exact_mod_cast hr0) (two_zpow_pos u)) hx₁
  have hy0 : 0 < y := lt_trans (mul_pos (by exact_mod_cast hr0) (two_zpow_pos u)) hy₁
  have hbx := binade_fine_interval hr0 hx₁ hx₂
  have hby := binade_fine_interval hr0 hy₁ hy₂
  have hb : F.M + 1 ≤ Nat.log2 r := (Nat.le_log2 (by omega)).2 hr
  let q : ℤ := max ((Nat.log2 r : ℤ) + u) F.emin - F.M
  have hq : u + 1 ≤ q := by
    have := le_max_left ((Nat.log2 r : ℤ) + u) F.emin
    dsimp [q]
    omega
  let c := 2 ^ (q - u - 1).toNat
  have hc : 0 < c := Nat.two_pow_pos _
  have hp : (2 : ℝ) ^ q = (2 * c) * 2 ^ u := by
    dsimp [c]
    rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]
    calc (2 : ℝ) ^ q = 2 ^ (q - u - 1 + 1 + u) := by congr 1; omega
      _ = 2 * 2 ^ (q - u - 1) * 2 ^ u := by
        rw [zpow_add₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_one]
        ring
  have hcancel (t : ℝ) : t / (2 * c) * ((2 * c) * 2 ^ u) = t * 2 ^ u := by
    have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
    field_simp
  have heq : rneNat (x / 2 ^ q) = rneNat (y / 2 ^ q) := by
    have hround (z : ℝ) (hz₁ : (r : ℝ) * 2 ^ u < z)
        (hz₂ : z < ((r : ℝ) + 1) * 2 ^ u) :
        rneNat (z / 2 ^ q) = (r / c + 1) / 2 := by
      apply rneNat_fine_interval hc
      · rw [lt_div_iff₀ (two_zpow_pos q), hp, hcancel]
        exact hz₁
      · rw [div_lt_iff₀ (two_zpow_pos q), hp, hcancel]
        exact hz₂
    rw [hround x hx₁ hx₂, hround y hy₁ hy₂]
  have hqx : ulpExp F x = q := by simp only [ulpExp, hbx, q]
  have hqy : ulpExp F y = q := by simp only [ulpExp, hby, q]
  simp only [gridRound, hx0.ne', hy0.ne', ↓reduceIte, abs_of_pos hx0, abs_of_pos hy0,
    hqx, hqy, not_lt_of_ge hx0.le, not_lt_of_ge hy0.le, decide_false, heq]

end FVA.Wasm.Num
