import FVA.Proof.Numerics.GridLemmas

/-!
# Rounding on the ulp grid

`ieee_N` (the spec) is stated through candidate pairs; `gridRound` rounds at the ulp of the
binade instead, the form the executable rounder computes and error bounds use. `ieee_iff_grid`
shows the two agree.
-/

namespace FVA.Wasm.Num

open FVal

/-- `⌊log₂ |r|⌋`, the binade of `r ≠ 0`. -/
noncomputable def binade (r : ℝ) : ℤ := Int.log 2 |r|

/-- The exponent of the unit in the last place at `r`: `max(binade r, emin) − M`. -/
noncomputable def ulpExp (F : FloatFormat) (r : ℝ) : ℤ := max (binade r) F.emin - F.M

/-- Round-half-even of a nonnegative real to a natural number. -/
noncomputable def rneNat (x : ℝ) : ℕ := (roundEven x).toNat

/-- Round `r` at the ulp grid of its binade, ties to even; overflow to `±∞` once the rounded
magnitude reaches `limit_N`; a zero keeps the sign of `r`. -/
noncomputable def gridRound (F : FloatFormat) (r : ℝ) : FVal :=
  if r = 0 then posZero else
  let q := ulpExp F r
  let m := rneNat (|r| / 2 ^ q)
  let s := decide (r < 0)
  if limit F ≤ (m : ℝ) * 2 ^ q then inf s
  else if m < 2 ^ F.M then subnormal s m
  else if m < 2 ^ (F.M + 1) then normal s (m - 2 ^ F.M) (q + F.M)
  else normal s 0 (q + F.M + 1)

/-- Formats with at least one significand bit and two exponent bits (f32, f64). -/
structure FloatFormat.Sane (F : FloatFormat) : Prop where
  /-- `M ≥ 1`. -/
  hM : 1 ≤ F.M
  /-- `E ≥ 2`. -/
  hE : 2 ≤ F.E

theorem f32fmt_sane : f32fmt.Sane := ⟨by decide, by decide⟩
theorem f64fmt_sane : f64fmt.Sane := ⟨by decide, by decide⟩

@[simp] lemma binade_neg (r : ℝ) : binade (-r) = binade r := by
  simp [binade]

@[simp] lemma ulpExp_neg (F : FloatFormat) (r : ℝ) : ulpExp F (-r) = ulpExp F r := by
  simp [ulpExp]

lemma gridRound_neg {F : FloatFormat} {r : ℝ} (hr : r ≠ 0) :
    gridRound F (-r) = fneg (gridRound F r) := by
  simp only [gridRound, hr, neg_ne_zero.mpr hr, ↓reduceIte, ulpExp_neg, abs_neg,
    sign_neg hr]
  split_ifs <;> rfl

lemma gridRound_positive {F : FloatFormat} {r : ℝ} (hr : 0 < r) :
    gridRound F r = positiveGrid F (max (binade r) F.emin)
      (roundEven (r / 2 ^ (max (binade r) F.emin - F.M))).toNat := by
  simp [gridRound, positiveGrid, ulpExp, rneNat, abs_of_pos hr, ne_of_gt hr,
    not_lt_of_ge hr.le]

lemma gridRound_ge_limit {F : FloatFormat} {r : ℝ} (hr : limit F ≤ r) :
    gridRound F r = inf false := by
  have hp : 0 < r := lt_of_lt_of_le (limit_pos F) hr
  have hb : F.emax + 1 ≤ binade r := by
    rw [binade, abs_of_pos hp]
    apply (Int.zpow_le_iff_le_log (by decide : 1 < (2 : ℕ)) hp).mp
    change (2 : ℝ) ^ (F.emax + 1) ≤ r
    rwa [← limit_eq_zpow]
  have he : F.emin ≤ binade r := le_trans (emin_le_emax_add_one F) hb
  have hmax : max (binade r) F.emin = binade r := max_eq_left he
  have hl : (2 : ℝ) ^ binade r ≤ r := by
    simpa [binade, abs_of_pos hp] using
      Int.zpow_log_le_self (by decide : 1 < (2 : ℕ)) hp
  have hu := two_zpow_pos (binade r - F.M)
  have hs : ((2 ^ F.M : ℕ) : ℝ) ≤ r / 2 ^ (binade r - F.M) := by
    apply (le_div_iff₀ hu).mpr
    rwa [scale_sig]
  have hm := roundEven_toNat_lower hs
  have hover : limit F ≤
      ((roundEven (r / 2 ^ (binade r - F.M))).toNat : ℝ) * 2 ^ (binade r - F.M) := by
    calc
      limit F ≤ (2 : ℝ) ^ binade r := by
        rw [limit_eq_zpow]
        exact zpow_le_zpow_right₀ (by norm_num) hb
      _ = ((2 ^ F.M : ℕ) : ℝ) * 2 ^ (binade r - F.M) := (scale_sig F _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hu.le
  rw [gridRound_positive hp, hmax]
  simp [positiveGrid, hover]

lemma ieee_iff_grid_positive {F : FloatFormat} (hF : F.Sane) {r : ℝ}
    (hr : 0 < r) (v : FVal) : Ieee F r v ↔ v = gridRound F r := by
  by_cases hlim : limit F ≤ r
  · rw [gridRound_ge_limit hlim]
    exact ieee_ge_limit_iff hlim
  · have hrl : r < limit F := lt_of_not_ge hlim
    have hblog : binade r ≤ F.emax := by
      have h := (Int.lt_zpow_iff_log_lt (by decide : 1 < (2 : ℕ)) hr).mp
        (by rwa [← limit_eq_zpow] : r < (2 : ℝ) ^ (F.emax + 1))
      simp only [binade, abs_of_pos hr]
      omega
    have he : max (binade r) F.emin ≤ F.emax :=
      max_le hblog (emin_le_emax hF.hE)
    have hupper : r < (2 : ℝ) ^ (max (binade r) F.emin + 1) := by
      have h := Int.lt_zpow_succ_log_self (by decide : 1 < (2 : ℕ)) r
      have h' : r < (2 : ℝ) ^ (binade r + 1) := by
        simpa [binade, abs_of_pos hr] using h
      apply lt_of_lt_of_le h'
      exact zpow_le_zpow_right₀ (by norm_num) (by have := le_max_left (binade r) F.emin; omega)
    have hlower : max (binade r) F.emin = F.emin ∨
        (2 : ℝ) ^ max (binade r) F.emin ≤ r := by
      by_cases hb : binade r ≤ F.emin
      · exact Or.inl (max_eq_right hb)
      · right
        rw [max_eq_left (le_of_not_ge hb)]
        simpa [binade, abs_of_pos hr] using
          Int.zpow_log_le_self (by decide : 1 < (2 : ℕ)) hr
    rw [gridRound_positive hr]
    exact ieee_local_grid_iff hF.hM (le_max_right _ _) he hr hupper hlower

/-- The candidate-pair spec and the ulp-grid rounder agree. -/
theorem ieee_iff_grid {F : FloatFormat} (hF : F.Sane) (r : ℝ) (v : FVal) :
    Ieee F r v ↔ v = gridRound F r := by
  by_cases hr : r = 0
  · subst r
    simpa [gridRound] using ieee_zero_iff F v
  by_cases hp : 0 < r
  · exact ieee_iff_grid_positive hF hp v
  have hn : 0 < -r := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hr)
  have h := ieee_iff_grid_positive hF hn (fneg v)
  rw [ieee_neg_iff hr, gridRound_neg hr] at h
  constructor
  · intro hv
    have he := congrArg fneg (h.mp hv)
    simpa using he
  · intro hv
    exact h.mpr (congrArg fneg hv)

end FVA.Wasm.Num
