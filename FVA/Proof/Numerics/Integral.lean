import FVA.Proof.Numerics.Arith
import FVA.Proof.Numerics.AdequacyLemmas

/-!
# Integral rounding returns allowed results

`Impl.fceil`, `ffloor`, `ftrunc`, `fnearest` on well-formed operands return an element of the
spec's set. A number with `ex ≥ 0` is already an integer and is returned unchanged; otherwise its
magnitude is `a / d` (`d = 2^(−ex)`), the impl picks the integer magnitude `k` from `a / d` and
`a % d`, and `k = 0` is exactly the spec's signed-zero case.
-/

namespace FVA.Wasm.Num

open FVal Impl

variable {F : FloatFormat}

theorem sig_lt {z : FVal} (hz : z.WF F) (hn : z.IsNum) : sig F z < 2 ^ (F.M + 1) := by
  cases z with
  | normal s m e => simp only [sig]; have := hz.1; rw [Nat.pow_succ]; omega
  | subnormal s m =>
    simp only [sig]; have : m < 2 ^ F.M := hz; rw [Nat.pow_succ]; omega
  | inf _ | nan _ _ => simp [IsNum] at hn

theorem emin_nonpos (hF : F.Sane) : F.emin ≤ 0 := by
  have h2 : (2 : ℤ) ≤ 2 ^ (F.E - 1) := by
    have : (2 : ℤ) ^ 1 ≤ 2 ^ (F.E - 1) := pow_le_pow_right₀ (by norm_num) (by have := hF.hE; omega)
    simpa using this
  unfold FloatFormat.emin; omega

/-- An integer of magnitude `1 ≤ k ≤ 2^M` rounds to itself. -/
theorem roundDyadic_int (hF : F.Wide) (s : Bool) {k : ℕ} (hk : 0 < k) (hk' : k ≤ 2 ^ F.M) :
    roundDyadic F s k 1 0 ∈
      {v : FVal | v.WF F ∧ v.IsNum ∧ v.toReal F = (if s then -1 else 1) * (k : ℝ)} := by
  have hlog : Nat.log2 k ≤ F.M := by
    have : k < 2 ^ (F.M + 1) := lt_of_le_of_lt hk' (Nat.pow_lt_pow_right (by norm_num) (by omega))
    have := (Nat.log2_lt (by omega)).2 this
    omega
  have h := roundDyadic_exact (e := 0) hF.toSane s hk
    (lt_of_le_of_lt hk' (Nat.pow_lt_pow_right (by norm_num) (by omega)))
    (by have := emin_nonpos hF.toSane; omega) (by have := hF.hEM; omega)
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.2, zpow_zero, mul_one]

theorem roundIntegral_ofNat {z : FVal} {j : ℕ} (hj : ex F z = Int.ofNat j)
    (pick : Bool → ℕ → ℕ → ℕ → ℕ) : roundIntegral F pick z = z := by
  unfold roundIntegral; rw [hj]

theorem roundIntegral_negSucc {z : FVal} {j : ℕ} (hj : ex F z = Int.negSucc j)
    (pick : Bool → ℕ → ℕ → ℕ → ℕ) :
    roundIntegral F pick z =
      let k := pick z.neg (sig F z / 2 ^ (j + 1)) (sig F z % 2 ^ (j + 1)) (2 ^ (j + 1))
      bif Nat.beq k 0 then subnormal z.neg 0 else roundDyadic F z.neg k 1 0 := by
  unfold roundIntegral; rw [hj]

/-- A number with `ex ≥ 0` is a nonzero integer. -/
theorem toReal_ofNat {z : FVal} (hn : z.IsNum) (h0 : ¬ z.IsZero) {j : ℕ}
    (hj : ex F z = Int.ofNat j) :
    ∃ t : ℤ, z.toReal F = t ∧ (1 ≤ t ∨ t ≤ -1) := by
  have hp := sig_pos (F := F) hn h0
  have hK : 1 ≤ sig F z * 2 ^ j := Nat.one_le_iff_ne_zero.2 (by positivity)
  refine ⟨(if z.neg then -1 else 1) * ((sig F z * 2 ^ j : ℕ) : ℤ), ?_, ?_⟩
  · rw [toReal_eq_sig z hn, hj, Int.ofNat_eq_natCast, zpow_natCast]; push_cast
    split <;> ring
  · have hK' : (1 : ℤ) ≤ ((sig F z * 2 ^ j : ℕ) : ℤ) := by exact_mod_cast hK
    split
    · right; omega
    · left; omega

/-- A number with `ex < 0` has magnitude `sig / 2^(−ex)`. -/
theorem toReal_negSucc {z : FVal} (hn : z.IsNum) {j : ℕ} (hj : ex F z = Int.negSucc j) :
    z.toReal F = (if z.neg then -1 else 1) * ((sig F z : ℝ) / ((2 ^ (j + 1) : ℕ) : ℝ)) := by
  have h : (Int.negSucc j : ℤ) = -((j + 1 : ℕ) : ℤ) := by rw [Int.negSucc_eq]; push_cast; ring
  rw [toReal_eq_sig z hn, hj, h, zpow_neg, zpow_natCast]
  push_cast; ring

/-- `roundEven` is odd. -/
theorem roundEven_neg (x : ℝ) : roundEven (-x) = -roundEven x := by
  unfold roundEven
  rw [Int.floor_neg, Int.ceil_neg]
  rcases eq_or_ne ⌊x⌋ ⌈x⌉ with h | h
  · have hx : (⌊x⌋ : ℝ) = x := by
      have h1 := Int.floor_le x
      have h2 := Int.le_ceil x
      rw [← h] at h2
      linarith
    have h1 : x - ⌊x⌋ < 1 / 2 := by linarith
    have h2 : -x - ((-⌈x⌉ : ℤ) : ℝ) < 1 / 2 := by rw [← h]; push_cast; linarith
    simp only [h1, h2, ↓reduceIte]
    rw [h]
  · have hc : ⌈x⌉ = ⌊x⌋ + 1 := by
      have := Int.ceil_le_floor_add_one x
      have := Int.floor_le_ceil x
      omega
    have hfr : -x - ((-⌈x⌉ : ℤ) : ℝ) = 1 - (x - ⌊x⌋) := by rw [hc]; push_cast; ring
    rw [hfr, hc]
    rcases lt_trichotomy (x - ⌊x⌋) (1 / 2) with hl | he | hg
    · have h1 : ¬ (1 - (x - ⌊x⌋) < 1 / 2) := by linarith
      have h2 : 1 - (x - ⌊x⌋) > 1 / 2 := by linarith
      simp only [hl, h1, h2, ↓reduceIte]
    · have h1 : ¬ (1 - (x - ⌊x⌋) < 1 / 2) := by linarith
      have h2 : ¬ (1 - (x - ⌊x⌋) > 1 / 2) := by linarith
      have h3 : ¬ (x - ⌊x⌋ < 1 / 2) := by linarith
      have h4 : ¬ (x - ⌊x⌋ > 1 / 2) := by linarith
      simp only [h1, h2, h3, h4, ↓reduceIte]
      rcases Int.emod_two_eq_zero_or_one ⌊x⌋ with hp | hp
      · have h5 : ¬ (-(⌊x⌋ + 1)) % 2 = 0 := by omega
        simp only [h5, hp, ↓reduceIte]
      · have h5 : (-(⌊x⌋ + 1)) % 2 = 0 := by omega
        have h6 : ¬ ⌊x⌋ % 2 = 0 := by omega
        simp only [h5, h6, ↓reduceIte]
    · have h1 : 1 - (x - ⌊x⌋) < 1 / 2 := by linarith
      have h3 : ¬ (x - ⌊x⌋ < 1 / 2) := by linarith
      simp only [h1, h3, hg, ↓reduceIte]

/-- The impl's integral rounding of a nonzero number: the integer `g r` when it is nonzero (an
exact float), else the zero of the operand's sign; `pick` must compute `g` on magnitudes. -/
theorem roundIntegral_mem (hF : F.Wide) {z : FVal} (hz : z.WF F) (hn : z.IsNum) (h0 : ¬ z.IsZero)
    (pick : Bool → ℕ → ℕ → ℕ → ℕ) (g : ℝ → ℤ) (hg : ∀ t : ℤ, g t = t)
    (hpick : ∀ (s : Bool) (a d : ℕ), 0 < a → 2 ≤ d → a < 2 ^ (F.M + 1) →
      ((if s then -1 else 1) * (pick s (a / d) (a % d) d : ℤ) =
        g ((if s then -1 else 1) * ((a : ℝ) / d))) ∧ pick s (a / d) (a % d) d ≤ 2 ^ F.M) :
    roundIntegral F pick z ∈
      (if g (z.toReal F) = 0 then ({subnormal z.neg 0} : Set FVal)
        else {v | v.WF F ∧ v.IsNum ∧ v.toReal F = g (z.toReal F)}) := by
  rcases hj : ex F z with j | j
  · rw [roundIntegral_ofNat hj]
    obtain ⟨t, ht, ht1⟩ := toReal_ofNat hn h0 hj
    have : t ≠ 0 := by omega
    rw [ht, hg]
    simp only [this, ↓reduceIte]
    exact ⟨hz, hn, ht⟩
  · rw [roundIntegral_negSucc hj, toReal_negSucc hn hj]
    have hd : 2 ≤ 2 ^ (j + 1) := by
      have : 2 ^ 1 ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using this
    obtain ⟨hk, hkb⟩ := hpick z.neg (sig F z) (2 ^ (j + 1)) (sig_pos hn h0) hd (sig_lt hz hn)
    rw [← hk]
    dsimp only
    generalize pick z.neg (sig F z / 2 ^ (j + 1)) (sig F z % 2 ^ (j + 1)) (2 ^ (j + 1)) = k at hkb ⊢
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    · have hne : (if z.neg then -1 else 1) * (k : ℤ) ≠ 0 := by
        cases z.neg <;> simp <;> omega
      have hb : Nat.beq k 0 = false := by
        cases k with
        | zero => omega
        | succ k => rfl
      simp only [hne, hb, ↓reduceIte, Bool.cond_false]
      have := roundDyadic_int hF z.neg hk0 hkb
      refine ⟨this.1, this.2.1, ?_⟩
      rw [this.2.2]
      cases z.neg <;> simp

/-- Magnitudes below `2^(M+1)` divided by `d ≥ 2` stay below `2^M`. -/
theorem div_lt_two_pow {a d M : ℕ} (ha : a < 2 ^ (M + 1)) (hd : 2 ≤ d) : a / d < 2 ^ M := by
  have : a / d ≤ a / 2 := Nat.div_le_div_left hd (by norm_num)
  have : a / 2 < 2 ^ M := by rw [Nat.pow_succ] at ha; omega
  omega

theorem natDiv_of_mod_zero {a d : ℕ} (hd : 0 < d) (h : a % d = 0) :
    (a : ℝ) / d = ((a / d : ℕ) : ℝ) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have : (a : ℝ) = d * (a / d : ℕ) := by
    have := Nat.div_add_mod a d
    exact_mod_cast (by omega : a = d * (a / d))
  rw [this]; field_simp

theorem ceil_natDiv' {a d : ℕ} (hd : 0 < d) :
    ⌈(a : ℝ) / d⌉ = ((if 0 < a % d then a / d + 1 else a / d : ℕ) : ℤ) := by
  split
  · rename_i h; rw [ceil_natDiv hd h]; push_cast; ring
  · rename_i h; rw [natDiv_of_mod_zero hd (by omega), Int.ceil_natCast]

theorem rneDiv_le {a d : ℕ} : rneDiv a d ≤ a / d + 1 := by
  unfold rneDiv
  dsimp only
  have : a / d % 2 ≤ 1 := by omega
  cases Nat.blt (2 * (a % d)) d <;> cases Nat.blt d (2 * (a % d)) <;>
    simp only [Bool.cond_true, Bool.cond_false] <;> omega

/-- The spec's special cases of `fceil` are its zero results. -/
theorem fceil_tail {z : FVal} (hn : z.IsNum) (hr : z.toReal F ≠ 0) :
    (if -1 < z.toReal F ∧ z.toReal F < 0 then ({negZero} : Set FVal)
      else {v | v.WF F ∧ v.IsNum ∧ v.toReal F = ((⌈z.toReal F⌉ : ℤ) : ℝ)}) =
    (if ⌈z.toReal F⌉ = 0 then {subnormal z.neg 0}
      else {v | v.WF F ∧ v.IsNum ∧ v.toReal F = ((⌈z.toReal F⌉ : ℤ) : ℝ)}) := by
  by_cases hc : ⌈z.toReal F⌉ = 0
  · obtain ⟨h1, h2⟩ := Int.ceil_eq_zero_iff.1 hc
    have hlt : z.toReal F < 0 := lt_of_le_of_ne h2 hr
    have hneg := (num_neg_iff hn hr).1 hlt
    simp [hc, h1, hlt, hneg, negZero]
  · have : ¬ (-1 < z.toReal F ∧ z.toReal F < 0) :=
      fun h => hc (Int.ceil_eq_zero_iff.2 ⟨h.1, h.2.le⟩)
    simp only [hc, this, ↓reduceIte]

/-- The spec's special case of `ffloor` is its zero result. -/
theorem ffloor_tail {z : FVal} (hn : z.IsNum) (hr : z.toReal F ≠ 0) :
    (if 0 < z.toReal F ∧ z.toReal F < 1 then ({posZero} : Set FVal)
      else {v | v.WF F ∧ v.IsNum ∧ v.toReal F = ((⌊z.toReal F⌋ : ℤ) : ℝ)}) =
    (if ⌊z.toReal F⌋ = 0 then {subnormal z.neg 0}
      else {v | v.WF F ∧ v.IsNum ∧ v.toReal F = ((⌊z.toReal F⌋ : ℤ) : ℝ)}) := by
  by_cases hc : ⌊z.toReal F⌋ = 0
  · obtain ⟨h1, h2⟩ := Int.floor_eq_zero_iff.1 hc
    have hlt : 0 < z.toReal F := lt_of_le_of_ne h1 hr.symm
    have hneg : z.neg = false := by
      have := (num_neg_iff hn hr).not.1 (not_lt.2 hlt.le); simpa using this
    simp [hc, h2, hlt, hneg, posZero]
  · have : ¬ (0 < z.toReal F ∧ z.toReal F < 1) :=
      fun h => hc (Int.floor_eq_zero_iff.2 ⟨h.1.le, h.2⟩)
    simp only [hc, this, ↓reduceIte]

/-- The spec's special cases of `ftrunc` are its zero results. -/
theorem ftrunc_tail {z : FVal} (hn : z.IsNum) (hr : z.toReal F ≠ 0) :
    (if 0 < z.toReal F ∧ z.toReal F < 1 then ({posZero} : Set FVal)
      else if -1 < z.toReal F ∧ z.toReal F < 0 then {negZero}
      else {v | v.WF F ∧ v.IsNum ∧ v.toReal F = ((truncR (z.toReal F) : ℤ) : ℝ)}) =
    (if truncR (z.toReal F) = 0 then {subnormal z.neg 0}
      else {v | v.WF F ∧ v.IsNum ∧ v.toReal F = ((truncR (z.toReal F) : ℤ) : ℝ)}) := by
  rcases lt_or_gt_of_ne hr with hlt | hgt
  · have hneg := (num_neg_iff hn hr).1 hlt
    have ht : truncR (z.toReal F) = ⌈z.toReal F⌉ := by simp [truncR, not_le.2 hlt]
    have hp : ¬ (0 < z.toReal F ∧ z.toReal F < 1) := fun h => absurd h.1 (not_lt.2 hlt.le)
    simp only [hp, ↓reduceIte, ht]
    by_cases hc : ⌈z.toReal F⌉ = 0
    · have h1 := (Int.ceil_eq_zero_iff.1 hc).1
      simp [hc, h1, hlt, hneg, negZero]
    · have : ¬ (-1 < z.toReal F ∧ z.toReal F < 0) :=
        fun h => hc (Int.ceil_eq_zero_iff.2 ⟨h.1, h.2.le⟩)
      simp only [hc, this, ↓reduceIte]
  · have hneg : z.neg = false := by
      have := (num_neg_iff hn hr).not.1 (not_lt.2 hgt.le); simpa using this
    have ht : truncR (z.toReal F) = ⌊z.toReal F⌋ := by simp [truncR, hgt.le]
    have hm : ¬ (-1 < z.toReal F ∧ z.toReal F < 0) := fun h => absurd h.2 (not_lt.2 hgt.le)
    simp only [hm, ↓reduceIte, ht]
    by_cases hc : ⌊z.toReal F⌋ = 0
    · have h2 := (Int.floor_eq_zero_iff.1 hc).2
      simp [hc, h2, hgt, hneg, posZero]
    · have : ¬ (0 < z.toReal F ∧ z.toReal F < 1) :=
        fun h => hc (Int.floor_eq_zero_iff.2 ⟨h.1.le, h.2⟩)
      simp only [hc, this, ↓reduceIte]

theorem roundEven_eq_zero {r : ℝ} (h1 : -1 / 2 ≤ r) (h2 : r ≤ 1 / 2) : roundEven r = 0 := by
  unfold roundEven
  rcases le_or_gt 0 r with h0 | h0
  · have hf : ⌊r⌋ = 0 := Int.floor_eq_zero_iff.2 ⟨h0, by linarith⟩
    rcases lt_or_eq_of_le h2 with hl | he
    · have : r - ⌊r⌋ < 1 / 2 := by rw [hf]; push_cast; linarith
      simp only [this, ↓reduceIte]
      exact hf
    · have h3 : ¬ (r - ⌊r⌋ < 1 / 2) := by rw [hf, he]; norm_num
      have h4 : ¬ (r - ⌊r⌋ > 1 / 2) := by rw [hf, he]; norm_num
      simp only [h3, h4, ↓reduceIte]
      simp [hf]
  · have hf : ⌊r⌋ = -1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have hc : ⌈r⌉ = 0 := Int.ceil_eq_zero_iff.2 ⟨by linarith, h0.le⟩
    have h3 : ¬ (r - ⌊r⌋ < 1 / 2) := by rw [hf]; push_cast; linarith
    rcases lt_or_eq_of_le h1 with hl | he
    · have h4 : r - ⌊r⌋ > 1 / 2 := by rw [hf]; push_cast; linarith
      simp only [h3, h4, ↓reduceIte, hc]
    · have h4 : ¬ (r - ⌊r⌋ > 1 / 2) := by rw [hf, ← he]; norm_num
      have h5 : ¬ (⌊r⌋ % 2 = 0) := by rw [hf]; decide
      simp only [h3, h4, h5, ↓reduceIte, hc]

/-- The spec's special cases of `fnearest` are its zero results. -/
theorem fnearest_tail {z : FVal} (hn : z.IsNum) (hr : z.toReal F ≠ 0) :
    (if 0 < z.toReal F ∧ z.toReal F ≤ 1 / 2 then ({posZero} : Set FVal)
      else if -1 / 2 ≤ z.toReal F ∧ z.toReal F < 0 then {negZero}
      else {v | v.WF F ∧ v.IsNum ∧ v.toReal F = ((roundEven (z.toReal F) : ℤ) : ℝ)}) =
    (if roundEven (z.toReal F) = 0 then {subnormal z.neg 0}
      else {v | v.WF F ∧ v.IsNum ∧ v.toReal F = ((roundEven (z.toReal F) : ℤ) : ℝ)}) := by
  by_cases hc : roundEven (z.toReal F) = 0
  · have hb := Adequacy.roundEven_zero_bounds hc
    rcases lt_or_gt_of_ne hr with hlt | hgt
    · have hneg := (num_neg_iff hn hr).1 hlt
      have hp : ¬ (0 < z.toReal F ∧ z.toReal F ≤ 1 / 2) := fun h => absurd h.1 (not_lt.2 hlt.le)
      have hm : -1 / 2 ≤ z.toReal F ∧ z.toReal F < 0 := ⟨hb.1, hlt⟩
      simp only [eq_false hp, eq_true hm, eq_true hc, ↓reduceIte, hneg]
      rfl
    · have hneg : z.neg = false := by
        have := (num_neg_iff hn hr).not.1 (not_lt.2 hgt.le); simpa using this
      have hp : 0 < z.toReal F ∧ z.toReal F ≤ 1 / 2 := ⟨hgt, hb.2⟩
      simp only [eq_true hp, eq_true hc, ↓reduceIte, hneg]
      rfl
  · have hp : ¬ (0 < z.toReal F ∧ z.toReal F ≤ 1 / 2) :=
      fun h => hc (roundEven_eq_zero (by linarith [h.1]) h.2)
    have hm : ¬ (-1 / 2 ≤ z.toReal F ∧ z.toReal F < 0) :=
      fun h => hc (roundEven_eq_zero h.1 (by linarith [h.2]))
    simp only [hc, hp, hm, ↓reduceIte]

open Classical in
/-- The shared case chain of the integral-rounding operators. -/
theorem integral_mem (hF : F.Wide) {z : FVal} (hz : z.WF F) (pick : Bool → ℕ → ℕ → ℕ → ℕ)
    (g : ℝ → ℤ) (hg : ∀ t : ℤ, g t = t)
    (hpick : ∀ (s : Bool) (a d : ℕ), 0 < a → 2 ≤ d → a < 2 ^ (F.M + 1) →
      ((if s then -1 else 1) * (pick s (a / d) (a % d) d : ℤ) =
        g ((if s then -1 else 1) * ((a : ℝ) / d))) ∧ pick s (a / d) (a % d) d ≤ 2 ^ F.M)
    (spec : Set FVal)
    (htail : z.IsNum → z.toReal F ≠ 0 → spec =
      (if g (z.toReal F) = 0 then {subnormal z.neg 0}
        else {v | v.WF F ∧ v.IsNum ∧ v.toReal F = ((g (z.toReal F) : ℤ) : ℝ)})) :
    (bif isNaN z then nanOf F [z] else bif isInf z || isZero z then z
      else roundIntegral F pick z) ∈
      (if z.IsNaN then nans F [z] else if z.IsInf ∨ z.IsZero then {z} else spec) := by
  by_cases hN : z.IsNaN
  · simp only [isNaN_iff.2 hN, Bool.cond_true, hN, ↓reduceIte]
    exact nanOf_mem hF.hM (by simp [hz])
  have hN' : isNaN z = false := by rw [← Bool.not_eq_true, isNaN_iff]; exact hN
  simp only [hN', Bool.cond_false, hN, ↓reduceIte]
  by_cases hI : z.IsInf ∨ z.IsZero
  · have : (isInf z || isZero z) = true := by
      rw [Bool.or_eq_true, isInf_iff, isZero_iff]; exact hI
    simp only [this, Bool.cond_true, hI, ↓reduceIte, Set.mem_singleton_iff]
  have hI' : (isInf z || isZero z) = false := by
    rw [← Bool.not_eq_true, Bool.or_eq_true, isInf_iff, isZero_iff]; exact hI
  simp only [hI', Bool.cond_false, hI, ↓reduceIte]
  have hn := Adequacy.num_of_not_nan_inf hN (fun h => hI (Or.inl h))
  have h0 : ¬ z.IsZero := fun h => hI (Or.inr h)
  rw [htail hn (Adequacy.num_nonzero hz hn h0)]
  exact roundIntegral_mem hF hz hn h0 pick g hg hpick

/-- Normalize the sign factors `if s then -1 else 1` of a picked magnitude. -/
macro (name := signNorm) "sign_norm" : tactic => `(tactic|
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul, Bool.not_false,
    Bool.not_true, Bool.true_and, Bool.false_and, Bool.cond_false])

theorem fceil_mem (hF : F.Wide) {z : FVal} (hz : z.WF F) : Impl.fceil F z ∈ fceil F z := by
  unfold Impl.fceil fceil
  refine integral_mem hF hz _ (fun r => ⌈r⌉) Int.ceil_intCast ?_ _ fceil_tail
  intro s a d ha hd hM
  have hd0 : 0 < d := by omega
  have hlt := div_lt_two_pow hM hd
  cases s <;> sign_norm
  · rw [ceil_natDiv' hd0]
    cases h : Nat.blt 0 (a % d)
    · have := nblt_false.1 h
      simp [show ¬ 0 < a % d by omega]; omega
    · have := nblt_true.1 h
      simp [this]; omega
  · rw [Int.ceil_neg, floor_natDiv hd0]
    simp; omega

theorem ffloor_mem (hF : F.Wide) {z : FVal} (hz : z.WF F) : Impl.ffloor F z ∈ ffloor F z := by
  unfold Impl.ffloor ffloor
  refine integral_mem hF hz _ (fun r => ⌊r⌋) Int.floor_intCast ?_ _ ffloor_tail
  intro s a d ha hd hM
  have hd0 : 0 < d := by omega
  have hlt := div_lt_two_pow hM hd
  cases s <;> sign_norm
  · rw [floor_natDiv hd0]
    simp; omega
  · rw [Int.floor_neg, ceil_natDiv' hd0]
    cases h : Nat.blt 0 (a % d)
    · have := nblt_false.1 h
      simp [show ¬ 0 < a % d by omega]; omega
    · have := nblt_true.1 h
      simp [this]; omega

theorem truncR_intCast (t : ℤ) : truncR (t : ℝ) = t := by
  unfold truncR
  split <;> simp

theorem ftrunc_mem (hF : F.Wide) {z : FVal} (hz : z.WF F) : Impl.ftrunc F z ∈ ftrunc F z := by
  unfold Impl.ftrunc ftrunc
  refine integral_mem hF hz _ truncR truncR_intCast ?_ _ ftrunc_tail
  intro s a d ha hd hM
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hpos : (0 : ℝ) < (a : ℝ) / d := div_pos (by exact_mod_cast ha) hdR
  have hlt := div_lt_two_pow hM hd
  refine ⟨?_, hlt.le⟩
  cases s <;> sign_norm
  · simp [truncR, hpos.le, floor_natDiv hd0]
  · have : ¬ (0 : ℝ) ≤ -((a : ℝ) / d) := by linarith
    simp [truncR, this, Int.ceil_neg, floor_natDiv hd0]

theorem roundEven_intCast (t : ℤ) : roundEven (t : ℝ) = t := by
  unfold roundEven
  simp

theorem fnearest_mem (hF : F.Wide) {z : FVal} (hz : z.WF F) :
    Impl.fnearest F z ∈ fnearest F z := by
  unfold Impl.fnearest fnearest
  refine integral_mem hF hz _ roundEven roundEven_intCast ?_ _ fnearest_tail
  intro s a d ha hd hM
  have hd0 : 0 < d := by omega
  have hlt := div_lt_two_pow hM hd
  have ha' : a / d * d + a % d = a := Nat.div_add_mod' a d
  simp only [ha']
  refine ⟨?_, by have := rneDiv_le (a := a) (d := d); omega⟩
  cases s <;> sign_norm
  · rw [roundEven_div hd0]
  · rw [roundEven_neg, roundEven_div hd0]

end FVA.Wasm.Num
