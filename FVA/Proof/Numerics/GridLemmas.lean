import FVA.Spec.Numerics.Float
import Mathlib.Data.Int.Log

/-! # Finite-value and nearest-integer lemmas for the ulp-grid proof -/

namespace FVA.Wasm.Num

open FVal

lemma two_zpow_pos (e : ℤ) : (0 : ℝ) < 2 ^ e := zpow_pos (by norm_num) e

lemma two_zpow_ne_zero (e : ℤ) : (2 : ℝ) ^ e ≠ 0 := ne_of_gt (two_zpow_pos e)

lemma scale_sig (F : FloatFormat) (e : ℤ) :
    ((2 ^ F.M : ℕ) : ℝ) * 2 ^ (e - F.M) = 2 ^ e := by
  rw [Nat.cast_pow, Nat.cast_ofNat, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0),
    zpow_natCast]
  field_simp

lemma limit_eq_zpow (F : FloatFormat) : limit F = (2 : ℝ) ^ (F.emax + 1) := by
  simp [limit, FloatFormat.emax, ← zpow_natCast]

lemma limit_pos (F : FloatFormat) : 0 < limit F := by
  rw [limit_eq_zpow]
  exact two_zpow_pos _

lemma toReal_normal (F : FloatFormat) (s : Bool) (m : ℕ) (e : ℤ) :
    (normal s m e).toReal F =
      (if s then -1 else 1) * ((2 ^ F.M : ℕ) + m : ℝ) * 2 ^ (e - F.M) := by
  rw [toReal, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, zpow_neg,
    zpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

lemma toReal_subnormal (F : FloatFormat) (s : Bool) (m : ℕ) :
    (subnormal s m).toReal F =
      (if s then -1 else 1) * (m : ℝ) * 2 ^ (F.emin - F.M) := by
  rw [toReal, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast,
    zpow_neg, zpow_natCast]
  ring

lemma abs_toReal_normal (F : FloatFormat) (s : Bool) (m : ℕ) (e : ℤ) :
    |(normal s m e).toReal F| = ((2 ^ F.M : ℕ) + m : ℝ) * 2 ^ (e - F.M) := by
  rw [toReal_normal, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 ^ F.M : ℕ) + m : ℝ)),
    abs_of_pos (two_zpow_pos _)]
  cases s <;> norm_num

lemma abs_toReal_subnormal (F : FloatFormat) (s : Bool) (m : ℕ) :
    |(subnormal s m).toReal F| = (m : ℝ) * 2 ^ (F.emin - F.M) := by
  rw [toReal_subnormal]
  cases s <;> simp [abs_mul, abs_of_pos (two_zpow_pos _)]

lemma normal_mag_bounds {F : FloatFormat} {s : Bool} {m : ℕ} {e : ℤ}
    (hm : m < 2 ^ F.M) :
    (2 : ℝ) ^ e ≤ |(normal s m e).toReal F| ∧
      |(normal s m e).toReal F| < (2 : ℝ) ^ (e + 1) := by
  rw [abs_toReal_normal, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have hs := scale_sig F e
  have hu := two_zpow_pos (e - F.M)
  have hm' : (m : ℝ) < (2 ^ F.M : ℕ) := by exact_mod_cast hm
  norm_num only [zpow_one]
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) m]

lemma subnormal_mag_bounds {F : FloatFormat} {s : Bool} {m : ℕ}
    (hm : m < 2 ^ F.M) :
    0 ≤ |(subnormal s m).toReal F| ∧
      |(subnormal s m).toReal F| < (2 : ℝ) ^ F.emin := by
  rw [abs_toReal_subnormal]
  have hs := scale_sig F F.emin
  have hu := two_zpow_pos (F.emin - F.M)
  have hm' : (m : ℝ) < (2 ^ F.M : ℕ) := by exact_mod_cast hm
  constructor
  · positivity
  · nlinarith

lemma log_eq_of_bounds {x : ℝ} {e : ℤ} (hx : 0 < x)
    (hl : (2 : ℝ) ^ e ≤ x) (hu : x < (2 : ℝ) ^ (e + 1)) :
    Int.log 2 x = e := by
  have h₁ := (Int.zpow_le_iff_le_log (by decide : 1 < (2 : ℕ)) hx).mp hl
  have h₂ := (Int.lt_zpow_iff_log_lt (by decide : 1 < (2 : ℕ)) hx).mp hu
  omega

lemma normal_log {F : FloatFormat} {s : Bool} {m : ℕ} {e : ℤ}
    (hm : m < 2 ^ F.M) : Int.log 2 |(normal s m e).toReal F| = e := by
  have h := normal_mag_bounds (s := s) (e := e) hm
  exact log_eq_of_bounds (lt_of_lt_of_le (two_zpow_pos e) h.1) h.1 h.2

lemma subnormal_log_lt {F : FloatFormat} {s : Bool} {m : ℕ}
    (hm : m < 2 ^ F.M) (hm0 : m ≠ 0) :
    Int.log 2 |(subnormal s m).toReal F| < F.emin := by
  have hp : 0 < |(subnormal s m).toReal F| := by
    rw [abs_toReal_subnormal]
    exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hm0) (two_zpow_pos _)
  exact (Int.lt_zpow_iff_log_lt (by decide : 1 < (2 : ℕ)) hp).mp
    (subnormal_mag_bounds hm).2

lemma emin_le_emax_add_one (F : FloatFormat) : F.emin ≤ F.emax + 1 := by
  have hp : (1 : ℤ) ≤ 2 ^ (F.E - 1) := one_le_pow₀ (by norm_num)
  simp only [FloatFormat.emin, FloatFormat.emax]
  omega

lemma emin_le_emax {F : FloatFormat} (hE : 2 ≤ F.E) : F.emin ≤ F.emax := by
  have hp : (2 : ℤ) ≤ 2 ^ (F.E - 1) := by
    calc
      2 = (2 : ℤ) ^ 1 := by norm_num
      _ ≤ 2 ^ (F.E - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  simp only [FloatFormat.emin, FloatFormat.emax]
  omega

lemma num_abs_lt_limit {F : FloatFormat} {v : FVal} (hw : v.WF F) (hn : v.IsNum) :
    |v.toReal F| < limit F := by
  rw [limit_eq_zpow]
  cases v with
  | normal s m e =>
    exact lt_of_lt_of_le (normal_mag_bounds hw.1).2
      (zpow_le_zpow_right₀ (by norm_num) (by have := hw.2.2; omega))
  | subnormal s m =>
    exact lt_of_lt_of_le (subnormal_mag_bounds hw).2
      (zpow_le_zpow_right₀ (by norm_num) (emin_le_emax_add_one F))
  | inf s => exact False.elim hn
  | nan s n => exact False.elim hn

lemma exact_abs_lt_limit {F : FloatFormat} {r : ℝ} (h : Exact F r) : |r| < limit F := by
  rcases h with ⟨v, hw, hn, rfl⟩
  exact num_abs_lt_limit hw hn

lemma candidate_abs_le_limit {F : FloatFormat} {r : ℝ} (h : Candidate F r) :
    |r| ≤ limit F := by
  rcases h with h | rfl | rfl
  · exact (exact_abs_lt_limit h).le
  · rw [abs_of_pos (limit_pos F)]
  · rw [abs_neg, abs_of_pos (limit_pos F)]

lemma exact_zero (F : FloatFormat) : Exact F 0 := by
  refine ⟨posZero, ?_, trivial, ?_⟩
  · exact Nat.two_pow_pos F.M
  · simp [posZero, toReal]

lemma candidate_zero (F : FloatFormat) : Candidate F 0 := Or.inl (exact_zero F)

lemma num_neg_iff {F : FloatFormat} {v : FVal} (hn : v.IsNum) (hz : v.toReal F ≠ 0) :
    v.toReal F < 0 ↔ v.neg = true := by
  cases v with
  | normal s m e =>
    rw [toReal_normal]
    have hp : (0 : ℝ) < ((2 ^ F.M : ℕ) + m : ℝ) * 2 ^ (e - F.M) :=
      mul_pos (by positivity) (two_zpow_pos _)
    cases s <;> simp only [neg, Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul,
      neg_lt_zero]
    · exact iff_false_intro (not_lt_of_ge hp.le)
    · exact iff_true_intro hp
  | subnormal s m =>
    rw [toReal_subnormal] at hz ⊢
    have hm : m ≠ 0 := by intro h; simp [h] at hz
    have hp : (0 : ℝ) < (m : ℝ) * 2 ^ (F.emin - F.M) := by
      exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hm) (two_zpow_pos _)
    cases s <;> simp only [neg, Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul,
      neg_lt_zero]
    · exact iff_false_intro (not_lt_of_ge hp.le)
    · exact iff_true_intro hp
  | inf s => exact False.elim hn
  | nan s n => exact False.elim hn

lemma num_eq_of_abs_eq {F : FloatFormat} {v w : FVal}
    (hv : v.WF F) (hnv : v.IsNum) (hw : w.WF F) (hnw : w.IsNum)
    (hs : v.neg = w.neg) (ha : |v.toReal F| = |w.toReal F|) : v = w := by
  cases v with
  | normal s m e =>
    cases w with
    | normal t n f =>
      have he : e = f := by
        rw [← normal_log (s := s) (e := e) hv.1, ha, normal_log hw.1]
      subst f
      have hm : m = n := by
        rw [abs_toReal_normal, abs_toReal_normal] at ha
        have h := (mul_right_cancel₀ (two_zpow_ne_zero (e - F.M)) ha)
        exact_mod_cast (add_left_cancel h)
      cases hs
      cases hm
      rfl
    | subnormal t n =>
      have hb := (normal_mag_bounds (s := s) (e := e) hv.1).1
      have ht := (subnormal_mag_bounds (s := t) hw).2
      have he : (2 : ℝ) ^ F.emin ≤ 2 ^ e :=
        zpow_le_zpow_right₀ (by norm_num) hv.2.1
      linarith
    | inf t => exact False.elim hnw
    | nan t n => exact False.elim hnw
  | subnormal s m =>
    cases w with
    | normal t n f =>
      have hb := (normal_mag_bounds (s := t) (e := f) hw.1).1
      have ht := (subnormal_mag_bounds (s := s) hv).2
      have he : (2 : ℝ) ^ F.emin ≤ 2 ^ f :=
        zpow_le_zpow_right₀ (by norm_num) hw.2.1
      linarith
    | subnormal t n =>
      have hm : m = n := by
        rw [abs_toReal_subnormal, abs_toReal_subnormal] at ha
        exact_mod_cast (mul_right_cancel₀ (two_zpow_ne_zero (F.emin - F.M)) ha)
      cases hs
      cases hm
      rfl
    | inf t => exact False.elim hnw
    | nan t n => exact False.elim hnw
  | inf s => exact False.elim hnv
  | nan s n => exact False.elim hnv

lemma num_eq_of_toReal_eq {F : FloatFormat} {v w : FVal}
    (hv : v.WF F) (hnv : v.IsNum) (hw : w.WF F) (hnw : w.IsNum)
    (hz : v.toReal F ≠ 0) (he : v.toReal F = w.toReal F) : v = w := by
  apply num_eq_of_abs_eq hv hnv hw hnw _ (congrArg abs he)
  have hwz : w.toReal F ≠ 0 := he ▸ hz
  have hs : (v.neg = true) ↔ (w.neg = true) := by
    rw [← num_neg_iff hnv hz, ← num_neg_iff hnw hwz, he]
  exact Bool.eq_iff_iff.mpr hs

@[simp] lemma fneg_fneg (v : FVal) : fneg (fneg v) = v := by
  cases v <;> simp [fneg, neg, withSign]

@[simp] lemma wf_fneg (F : FloatFormat) (v : FVal) : (fneg v).WF F ↔ v.WF F := by
  cases v <;> rfl

@[simp] lemma isNum_fneg (v : FVal) : (fneg v).IsNum ↔ v.IsNum := by
  cases v <;> rfl

@[simp] lemma sigField_fneg (v : FVal) : (fneg v).sigField = v.sigField := by
  cases v <;> rfl

lemma toReal_fneg (F : FloatFormat) (v : FVal) : (fneg v).toReal F = -v.toReal F := by
  cases v with
  | normal s m e => cases s <;> simp [fneg, neg, withSign, toReal] <;> ring
  | subnormal s m => cases s <;> simp [fneg, neg, withSign, toReal]
  | inf s => simp [fneg, neg, withSign, toReal]
  | nan s n => simp [fneg, neg, withSign, toReal]

lemma exact_neg {F : FloatFormat} {x : ℝ} (h : Exact F x) : Exact F (-x) := by
  rcases h with ⟨v, hw, hn, hv⟩
  exact ⟨fneg v, (wf_fneg F v).mpr hw, (isNum_fneg v).mpr hn, by rw [toReal_fneg, hv]⟩

@[simp] lemma exact_neg_iff (F : FloatFormat) (x : ℝ) : Exact F (-x) ↔ Exact F x := by
  constructor
  · intro h; simpa using exact_neg h
  · exact exact_neg

lemma candidate_neg {F : FloatFormat} {x : ℝ} (h : Candidate F x) :
    Candidate F (-x) := by
  rcases h with h | rfl | rfl
  · exact Or.inl (exact_neg h)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl (neg_neg _))

@[simp] lemma candidate_neg_iff (F : FloatFormat) (x : ℝ) :
    Candidate F (-x) ↔ Candidate F x := by
  constructor
  · intro h; simpa using candidate_neg h
  · exact candidate_neg

lemma evenCand_neg {F : FloatFormat} {x : ℝ} (h : EvenCand F x) : EvenCand F (-x) := by
  rcases h with rfl | rfl | ⟨v, hw, hn, hv, he⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl (neg_neg _)
  · exact Or.inr (Or.inr ⟨fneg v, (wf_fneg F v).mpr hw, (isNum_fneg v).mpr hn,
      by rw [toReal_fneg, hv], by simpa using he⟩)

@[simp] lemma evenCand_neg_iff (F : FloatFormat) (x : ℝ) :
    EvenCand F (-x) ↔ EvenCand F x := by
  constructor
  · intro h; simpa using evenCand_neg h
  · exact evenCand_neg

lemma candidatePair_neg {F : FloatFormat} {x y : ℝ} (h : CandidatePair F x y) :
    CandidatePair F (-y) (-x) := by
  refine ⟨candidate_neg h.2.1, candidate_neg h.1, neg_lt_neg h.2.2.1, ?_⟩
  intro z hz
  rcases h.2.2.2 (-z) (candidate_neg hz) with hx | hy
  · right; linarith
  · left; linarith

lemma sign_neg {r : ℝ} (hr : r ≠ 0) : decide (-r < 0) = !decide (r < 0) := by
  by_cases hp : 0 < r
  · simp [hp, not_lt_of_ge hp.le]
  · have hn : r < 0 := lt_of_le_of_ne (le_of_not_gt hp) hr
    simp [hn, not_lt_of_ge hn.le]

lemma rectify_neg {F : FloatFormat} {r z : ℝ} {v : FVal} (hr : r ≠ 0)
    (h : Rectify F r z v) : Rectify F (-r) (-z) (fneg v) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨hz, hp, hn, hw, hv, he⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inl ⟨neg_neg _, rfl⟩
  · exact Or.inr (Or.inr (Or.inl ⟨neg_zero,
      by simp only [fneg, neg, withSign]; rw [sign_neg hr]⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨neg_ne_zero.mpr hz, ?_, ?_,
      (wf_fneg F v).mpr hw, (isNum_fneg v).mpr hv, ?_⟩))
    · intro h; apply hn; linarith
    · exact fun h => hp (neg_injective h)
    · rw [toReal_fneg, he]

lemma closest_neg {F : FloatFormat} {r x y : ℝ} {v : FVal} (hr : r ≠ 0)
    (h : Closest F r x y v) : Closest F (-r) (-y) (-x) (fneg v) := by
  have hx : |-r - -x| = |r - x| := by rw [neg_sub_neg, abs_sub_comm]
  have hy : |-r - -y| = |r - y| := by rw [neg_sub_neg, abs_sub_comm]
  rcases h with ⟨h, hv⟩ | ⟨h, hv⟩ | ⟨h, he, hv⟩ | ⟨h, he, hv⟩
  · exact Or.inr (Or.inl ⟨by rw [hx, hy]; exact h, rectify_neg hr hv⟩)
  · exact Or.inl ⟨by rw [hx, hy]; exact h, rectify_neg hr hv⟩
  · exact Or.inr (Or.inr (Or.inr ⟨by rw [hx, hy]; exact h.symm,
      evenCand_neg he, rectify_neg hr hv⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨by rw [hx, hy]; exact h.symm,
      evenCand_neg he, rectify_neg hr hv⟩))

lemma ieee_neg {F : FloatFormat} {r : ℝ} {v : FVal} (hr : r ≠ 0)
    (h : Ieee F r v) : Ieee F (-r) (fneg v) := by
  rcases h with ⟨h, _⟩ | ⟨_, hx, hw, hn, he⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ |
    ⟨x, y, hp, hl, hu, hc⟩
  · exact False.elim (hr h)
  · exact Or.inr (Or.inl ⟨neg_ne_zero.mpr hr, exact_neg hx,
      (wf_fneg F v).mpr hw, (isNum_fneg v).mpr hn, by rw [toReal_fneg, he]⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨by linarith, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨-y, -x, candidatePair_neg hp,
      by linarith, by linarith, closest_neg hr hc⟩)))

lemma ieee_neg_iff {F : FloatFormat} {r : ℝ} {v : FVal} (hr : r ≠ 0) :
    Ieee F (-r) (fneg v) ↔ Ieee F r v := by
  constructor
  · intro h
    simpa using ieee_neg (neg_ne_zero.mpr hr) h
  · exact ieee_neg hr

lemma num_ne_limits {F : FloatFormat} {v : FVal} (hw : v.WF F) (hn : v.IsNum) :
    v.toReal F ≠ limit F ∧ v.toReal F ≠ -limit F := by
  have h := num_abs_lt_limit hw hn
  constructor <;> intro he <;> rw [he] at h
  · rw [abs_of_pos (limit_pos F)] at h
    exact lt_irrefl _ h
  · rw [abs_neg, abs_of_pos (limit_pos F)] at h
    exact lt_irrefl _ h

lemma evenCand_num_iff {F : FloatFormat} {v : FVal} (hw : v.WF F) (hn : v.IsNum)
    (hz : v.toReal F ≠ 0) : EvenCand F (v.toReal F) ↔ v.sigField % 2 = 0 := by
  have hlim := num_ne_limits hw hn
  constructor
  · rintro (hp | hm | ⟨w, hww, hwn, he, hpar⟩)
    · exact False.elim (hlim.1 hp)
    · exact False.elim (hlim.2 hm)
    · have heq := num_eq_of_toReal_eq hw hn hww hwn hz he.symm
      simpa [heq] using hpar
  · intro hp
    exact Or.inr (Or.inr ⟨v, hw, hn, rfl, hp⟩)

lemma rectify_num_iff {F : FloatFormat} {r : ℝ} {v w : FVal}
    (hw : v.WF F) (hn : v.IsNum) (hz : v.toReal F ≠ 0) :
    Rectify F r (v.toReal F) w ↔ w = v := by
  have hlim := num_ne_limits hw hn
  constructor
  · rintro (⟨hp, _⟩ | ⟨hm, _⟩ | ⟨h0, _⟩ | ⟨_, _, _, hww, hwn, he⟩)
    · exact False.elim (hlim.1 hp)
    · exact False.elim (hlim.2 hm)
    · exact False.elim (hz h0)
    · exact (num_eq_of_toReal_eq hw hn hww hwn hz he.symm).symm
  · rintro rfl
    exact Or.inr (Or.inr (Or.inr ⟨hz, hlim.1, hlim.2, hw, hn, rfl⟩))

lemma rectify_zero_iff (F : FloatFormat) (r : ℝ) (v : FVal) :
    Rectify F r 0 v ↔ v = subnormal (decide (r < 0)) 0 := by
  have h := limit_pos F
  simp only [Rectify]
  constructor
  · rintro (⟨hp, _⟩ | ⟨hm, _⟩ | ⟨_, hv⟩ | ⟨h0, _⟩)
    · linarith
    · linarith
    · exact hv
    · exact False.elim (h0 rfl)
  · intro hv
    exact Or.inr (Or.inr (Or.inl ⟨trivial, hv⟩))

lemma rectify_limit_iff (F : FloatFormat) (r : ℝ) (v : FVal) :
    Rectify F r (limit F) v ↔ v = inf false := by
  have h := limit_pos F
  constructor
  · rintro (⟨_, hv⟩ | ⟨hm, _⟩ | ⟨h0, _⟩ | ⟨_, hp, _⟩)
    · exact hv
    · linarith
    · linarith
    · exact False.elim (hp rfl)
  · intro hv
    exact Or.inl ⟨rfl, hv⟩

lemma candidatePair_unique {F : FloatFormat} {a b c d r : ℝ}
    (hab : CandidatePair F a b) (hcd : CandidatePair F c d)
    (ha : a < r) (hb : r < b) (hc : c < r) (hd : r < d) : a = c ∧ b = d := by
  have hac := hab.2.2.2 c hcd.1
  have had := hab.2.2.2 d hcd.2.1
  have hca := hcd.2.2.2 a hab.1
  have hcb := hcd.2.2.2 b hab.2.1
  constructor <;> rcases hac with hac | hac <;> rcases had with had | had <;>
    rcases hca with hca | hca <;> rcases hcb with hcb | hcb <;> linarith

lemma ieee_iff_closest {F : FloatFormat} {r a b : ℝ} {v : FVal}
    (hp : CandidatePair F a b) (ha : a < r) (hb : r < b) :
    Ieee F r v ↔ Closest F r a b v := by
  have hnot : ¬ Candidate F r := by
    intro h
    rcases hp.2.2.2 r h with h | h <;> linarith
  constructor
  · rintro (⟨hr, _⟩ | ⟨_, he, _⟩ | ⟨hr, _⟩ | ⟨hr, _⟩ | ⟨c, d, hcd, hc, hd, hv⟩)
    · exact False.elim (hnot (hr ▸ candidate_zero F))
    · exact False.elim (hnot (Or.inl he))
    · have hlim := candidate_abs_le_limit hp.2.1
      have hle := le_abs_self b
      linarith
    · have hlim := candidate_abs_le_limit hp.1
      have hle := neg_abs_le a
      linarith
    · obtain ⟨rfl, rfl⟩ := candidatePair_unique hp hcd ha hb hc hd
      exact hv
  · intro hv
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, b, hp, ha, hb, hv⟩)))

lemma ieee_exact_iff {F : FloatFormat} {r : ℝ} {v w : FVal}
    (hw : w.WF F) (hn : w.IsNum) (he : w.toReal F = r) (hr : r ≠ 0) :
    Ieee F r v ↔ v = w := by
  have hx : Exact F r := ⟨w, hw, hn, he⟩
  have hlim := exact_abs_lt_limit hx
  constructor
  · rintro (⟨h0, _⟩ | ⟨_, _, hv, hvn, hve⟩ | ⟨h, _⟩ | ⟨h, _⟩ |
      ⟨a, b, hp, ha, hb, _⟩)
    · exact False.elim (hr h0)
    · exact num_eq_of_toReal_eq hv hvn hw hn (by rw [hve]; exact hr) (hve.trans he.symm)
    · have hle := le_abs_self r
      linarith
    · have hle := neg_abs_le r
      linarith
    · rcases hp.2.2.2 r (Or.inl hx) with h | h <;> linarith
  · rintro rfl
    exact Or.inr (Or.inl ⟨hr, hx, hw, hn, he⟩)

lemma ieee_zero_iff (F : FloatFormat) (v : FVal) : Ieee F 0 v ↔ v = posZero := by
  have hlim := limit_pos F
  constructor
  · rintro (⟨_, hv⟩ | ⟨h0, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨a, b, hp, ha, hb, _⟩)
    · exact hv
    · exact False.elim (h0 rfl)
    · linarith
    · linarith
    · rcases hp.2.2.2 0 (candidate_zero F) with h | h <;> linarith
  · intro hv
    exact Or.inl ⟨rfl, hv⟩

lemma ieee_ge_limit_iff {F : FloatFormat} {r : ℝ} {v : FVal} (hr : limit F ≤ r) :
    Ieee F r v ↔ v = inf false := by
  have hp := limit_pos F
  constructor
  · rintro (⟨h0, _⟩ | ⟨_, he, _⟩ | ⟨_, hv⟩ | ⟨h, _⟩ | ⟨a, b, hpair, _, hb, _⟩)
    · linarith
    · have he := exact_abs_lt_limit he
      have ha := le_abs_self r
      linarith
    · exact hv
    · linarith
    · have he := candidate_abs_le_limit hpair.2.1
      have ha := le_abs_self b
      linarith
  · intro hv
    exact Or.inr (Or.inr (Or.inl ⟨hr, hv⟩))

/-- The positive result represented by a local ulp index, including carry and overflow. -/
noncomputable def positiveGrid (F : FloatFormat) (e : ℤ) (m : ℕ) : FVal :=
  if limit F ≤ (m : ℝ) * 2 ^ (e - F.M) then inf false
  else if m < 2 ^ F.M then subnormal false m
  else if m < 2 ^ (F.M + 1) then normal false (m - 2 ^ F.M) e
  else normal false 0 (e + 1)

/-- Local grid indices include the next binade's first point, or the positive limit. -/
structure GridIndex (F : FloatFormat) (e : ℤ) (m : ℕ) : Prop where
  lower : F.emin ≤ e
  upper : e ≤ F.emax
  bound : m ≤ 2 ^ (F.M + 1)
  small : m < 2 ^ F.M → e = F.emin

lemma num_zero_eq {F : FloatFormat} {v : FVal} (hw : v.WF F) (hn : v.IsNum)
    (hz : v.toReal F = 0) : v = subnormal v.neg 0 := by
  apply num_eq_of_abs_eq (w := subnormal v.neg 0) hw hn (Nat.two_pow_pos _) trivial rfl
  rw [hz]
  simp [toReal]

lemma evenCand_num_iff_all {F : FloatFormat} {v : FVal} (hw : v.WF F) (hn : v.IsNum) :
    EvenCand F (v.toReal F) ↔ v.sigField % 2 = 0 := by
  by_cases hz : v.toReal F = 0
  · have he := num_zero_eq hw hn hz
    have hpar : v.sigField % 2 = 0 := by rw [he]; rfl
    exact iff_of_true (Or.inr (Or.inr ⟨v, hw, hn, rfl, hpar⟩)) hpar
  · exact evenCand_num_iff hw hn hz

lemma rectify_positive_num_iff {F : FloatFormat} {r : ℝ} {v w : FVal}
    (hr : 0 < r) (hw : v.WF F) (hn : v.IsNum) (hs : v.neg = false) :
    Rectify F r (v.toReal F) w ↔ w = v := by
  by_cases hz : v.toReal F = 0
  · have he : v = posZero := by simpa [hs, posZero] using num_zero_eq hw hn hz
    rw [hz, rectify_zero_iff, he]
    simp [not_lt_of_ge hr.le, posZero]
  · exact rectify_num_iff hw hn hz

lemma two_pow_mod_two {M : ℕ} (hM : 1 ≤ M) : 2 ^ M % 2 = 0 := by
  rw [Nat.pow_mod]
  simp [Nat.ne_of_gt hM]

lemma sub_two_pow_mod_two {M m : ℕ} (hM : 1 ≤ M) (hm : 2 ^ M ≤ m) :
    (m - 2 ^ M) % 2 = m % 2 := by
  have h := congrArg (· % 2) (Nat.sub_add_cancel hm)
  simpa [Nat.add_mod, two_pow_mod_two hM] using h

lemma scale_sig_succ (F : FloatFormat) (e : ℤ) :
    ((2 ^ (F.M + 1) : ℕ) : ℝ) * 2 ^ (e - F.M) = 2 ^ (e + 1) := by
  rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  nlinarith [scale_sig F e]

lemma positiveGrid_spec {F : FloatFormat} {e : ℤ} {m : ℕ}
    (hM : 1 ≤ F.M) (hi : GridIndex F e m) :
    Candidate F ((m : ℝ) * 2 ^ (e - F.M)) ∧
    (EvenCand F ((m : ℝ) * 2 ^ (e - F.M)) ↔ m % 2 = 0) ∧
    ∀ r : ℝ, 0 < r → ∀ v : FVal,
      Rectify F r ((m : ℝ) * 2 ^ (e - F.M)) v ↔ v = positiveGrid F e m := by
  have finite : ∀ w : FVal, w.WF F → w.IsNum → w.neg = false →
      w.toReal F = (m : ℝ) * 2 ^ (e - F.M) → w.sigField % 2 = m % 2 →
      positiveGrid F e m = w →
      Candidate F ((m : ℝ) * 2 ^ (e - F.M)) ∧
      (EvenCand F ((m : ℝ) * 2 ^ (e - F.M)) ↔ m % 2 = 0) ∧
      ∀ r : ℝ, 0 < r → ∀ v : FVal,
        Rectify F r ((m : ℝ) * 2 ^ (e - F.M)) v ↔ v = positiveGrid F e m := by
    intro w hw hn hs he hp hv
    rw [← he, hv]
    exact ⟨Or.inl ⟨w, hw, hn, rfl⟩,
      by rw [evenCand_num_iff_all hw hn, hp],
      fun _ hr _ => rectify_positive_num_iff hr hw hn hs⟩
  by_cases hm : m < 2 ^ F.M
  · have he := hi.small hm
    have hw : (subnormal false m).WF F := hm
    have hv : (subnormal false m).toReal F = (m : ℝ) * 2 ^ (e - F.M) := by
      rw [toReal_subnormal, he]
      simp
    have hb : (m : ℝ) * 2 ^ (e - F.M) < limit F := by
      rw [← hv]
      exact lt_of_le_of_lt (le_abs_self _) (num_abs_lt_limit hw trivial)
    apply finite (subnormal false m) hw trivial rfl hv rfl
    simp [positiveGrid, not_le_of_gt hb, hm]
  · by_cases hm' : m < 2 ^ (F.M + 1)
    · have hmb : 2 ^ F.M ≤ m := Nat.le_of_not_gt hm
      have hw : (normal false (m - 2 ^ F.M) e).WF F := by
        refine ⟨?_, hi.lower, hi.upper⟩
        rw [pow_succ] at hm'
        omega
      have hv : (normal false (m - 2 ^ F.M) e).toReal F =
          (m : ℝ) * 2 ^ (e - F.M) := by
        rw [toReal_normal, Nat.cast_sub hmb]
        simp
      have hb : (m : ℝ) * 2 ^ (e - F.M) < limit F := by
        rw [← hv]
        exact lt_of_le_of_lt (le_abs_self _) (num_abs_lt_limit hw trivial)
      apply finite (normal false (m - 2 ^ F.M) e) hw trivial rfl hv
        (sub_two_pow_mod_two hM hmb)
      simp [positiveGrid, not_le_of_gt hb, hm, hm']
    · have hme : m = 2 ^ (F.M + 1) := by have := hi.bound; omega
      have hv : (m : ℝ) * 2 ^ (e - F.M) = (2 : ℝ) ^ (e + 1) := by
        rw [hme, scale_sig_succ]
      have hp : m % 2 = 0 := hme ▸ two_pow_mod_two (by omega)
      by_cases he : e = F.emax
      · have hz : (m : ℝ) * 2 ^ (e - F.M) = limit F := by
          rw [hv, he, limit_eq_zpow]
        have hg : positiveGrid F e m = inf false := by simp [positiveGrid, hz]
        rw [hz, hg]
        exact ⟨Or.inr (Or.inl rfl), iff_of_true (Or.inl rfl) hp,
          fun r _ v => rectify_limit_iff F r v⟩
      · have hw : (normal false 0 (e + 1)).WF F := by
          refine ⟨Nat.two_pow_pos _, ?_, ?_⟩ <;>
            have := hi.lower <;> have := hi.upper <;> omega
        have hval : (normal false 0 (e + 1)).toReal F =
            (m : ℝ) * 2 ^ (e - F.M) := by rw [hv]; simp [toReal]
        have hb : (m : ℝ) * 2 ^ (e - F.M) < limit F := by
          rw [← hval]
          exact lt_of_le_of_lt (le_abs_self _) (num_abs_lt_limit hw trivial)
        apply finite (normal false 0 (e + 1)) hw trivial rfl hval
          (by simpa only [sigField, Nat.zero_mod] using hp.symm)
        simp [positiveGrid, not_le_of_gt hb, hm, hm']

lemma exact_grid_integer {F : FloatFormat} {e : ℤ} {z : ℝ}
    (he : F.emin ≤ e) (hz : 0 ≤ z) (hu : z < (2 : ℝ) ^ (e + 1))
    (hl : e = F.emin ∨ (2 : ℝ) ^ e ≤ z) (hx : Exact F z) :
    ∃ n : ℕ, z = (n : ℝ) * 2 ^ (e - F.M) := by
  rcases hx with ⟨v, hw, hn, hv⟩
  have ha : |v.toReal F| = z := by rw [hv, abs_of_nonneg hz]
  cases v with
  | normal s m f =>
    have hpos : 0 < z := by
      have hb := (normal_mag_bounds (s := s) (e := f) hw.1).1
      rw [ha] at hb
      exact lt_of_lt_of_le (two_zpow_pos _) hb
    have hlog : Int.log 2 z = f := by rw [← ha]; exact normal_log hw.1
    have hfe : f ≤ e := by
      have h := (Int.lt_zpow_iff_log_lt (by decide : 1 < (2 : ℕ)) hpos).mp hu
      rw [hlog] at h
      omega
    have hef : e ≤ f := by
      rcases hl with h | h
      · rw [h]
        exact hw.2.1
      · have h' := (Int.zpow_le_iff_le_log (by decide : 1 < (2 : ℕ)) hpos).mp h
        rwa [hlog] at h'
    have hfeq : f = e := le_antisymm hfe hef
    refine ⟨2 ^ F.M + m, ?_⟩
    rw [← ha, abs_toReal_normal, hfeq, Nat.cast_add]
  | subnormal s m =>
    have heq : e = F.emin := by
      rcases hl with h | h
      · exact h
      · have hb := (subnormal_mag_bounds (s := s) hw).2
        rw [ha] at hb
        have hs : (2 : ℝ) ^ F.emin ≤ 2 ^ e := zpow_le_zpow_right₀ (by norm_num) he
        linarith
    refine ⟨m, ?_⟩
    rw [← ha, abs_toReal_subnormal, heq]
  | inf s => exact False.elim hn
  | nan s n => exact False.elim hn

lemma candidate_grid_integer {F : FloatFormat} {e : ℤ} {z : ℝ}
    (he : F.emin ≤ e) (he' : e ≤ F.emax) (hz : 0 ≤ z)
    (hu : z < (2 : ℝ) ^ (e + 1)) (hl : e = F.emin ∨ (2 : ℝ) ^ e ≤ z)
    (hc : Candidate F z) : ∃ n : ℕ, z = (n : ℝ) * 2 ^ (e - F.M) := by
  rcases hc with hx | hp | hn
  · exact exact_grid_integer he hz hu hl hx
  · have hb : (2 : ℝ) ^ (e + 1) ≤ limit F := by
      rw [limit_eq_zpow]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  · have hp := limit_pos F
    linarith

lemma gridIndex_next {F : FloatFormat} {e : ℤ} {m : ℕ}
    (hi : GridIndex F e m) (hm : m < 2 ^ (F.M + 1)) : GridIndex F e (m + 1) := by
  refine ⟨hi.lower, hi.upper, by omega, ?_⟩
  intro h
  exact hi.small (by omega)

lemma grid_adjacent {F : FloatFormat} {e : ℤ} {m : ℕ}
    (hM : 1 ≤ F.M) (hi : GridIndex F e m) (hm : m < 2 ^ (F.M + 1)) :
    CandidatePair F ((m : ℝ) * 2 ^ (e - F.M))
      (((m + 1 : ℕ) : ℝ) * 2 ^ (e - F.M)) := by
  have hs := positiveGrid_spec hM hi
  have ht := positiveGrid_spec hM (gridIndex_next hi hm)
  have hu := two_zpow_pos (e - F.M)
  refine ⟨hs.1, ht.1, ?_, ?_⟩
  · exact mul_lt_mul_of_pos_right (by norm_num) hu
  · intro z hz
    by_cases hl : z ≤ (m : ℝ) * 2 ^ (e - F.M)
    · exact Or.inl hl
    by_cases hh : ((m + 1 : ℕ) : ℝ) * 2 ^ (e - F.M) ≤ z
    · exact Or.inr hh
    exfalso
    have hzl : (m : ℝ) * 2 ^ (e - F.M) < z := lt_of_not_ge hl
    have hzh : z < ((m + 1 : ℕ) : ℝ) * 2 ^ (e - F.M) := lt_of_not_ge hh
    have hz0 : 0 ≤ z := le_of_lt (lt_of_le_of_lt (by positivity) hzl)
    have htop : z < (2 : ℝ) ^ (e + 1) := by
      rw [← scale_sig_succ F e]
      exact lt_of_lt_of_le hzh (mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hu.le)
    have hlow : e = F.emin ∨ (2 : ℝ) ^ e ≤ z := by
      by_cases hmb : m < 2 ^ F.M
      · exact Or.inl (hi.small hmb)
      · right
        rw [← scale_sig F e]
        exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_not_gt hmb)
          hu.le) hzl.le
    obtain ⟨n, rfl⟩ := candidate_grid_integer hi.lower hi.upper hz0 htop hlow hz
    have hmn : m < n := by exact_mod_cast (mul_lt_mul_iff_left₀ hu).mp hzl
    have hnm : n < m + 1 := by exact_mod_cast (mul_lt_mul_iff_left₀ hu).mp hzh
    omega

lemma roundEven_natCast (m : ℕ) : roundEven (m : ℝ) = m := by
  simp [roundEven]

lemma roundEven_toNat_lower {x : ℝ} {m : ℕ} (hm : (m : ℝ) ≤ x) :
    m ≤ (roundEven x).toNat := by
  have hfl : (m : ℤ) ≤ ⌊x⌋ := Int.le_floor.mpr (by exact_mod_cast hm)
  have hce : (m : ℤ) ≤ ⌈x⌉ := by
    exact_mod_cast le_trans hm (Int.le_ceil x)
  unfold roundEven
  split_ifs <;> omega

lemma roundEven_toNat_upper {x : ℝ} {m : ℕ} (hm : x ≤ (m : ℝ)) :
    (roundEven x).toNat ≤ m := by
  have hfl : ⌊x⌋ ≤ (m : ℤ) := by
    exact_mod_cast le_trans (Int.floor_le x) hm
  have hce : ⌈x⌉ ≤ (m : ℤ) := Int.ceil_le.mpr (by exact_mod_cast hm)
  unfold roundEven
  split_ifs <;> omega

lemma roundEven_toNat_between {x : ℝ} {m : ℕ} (hl : (m : ℝ) < x)
    (hu : x < m + 1) :
    (roundEven x).toNat =
      if x - m < 1 / 2 then m
      else if x - m > 1 / 2 then m + 1
      else if m % 2 = 0 then m else m + 1 := by
  have hf : ⌊x⌋ = (m : ℤ) := Int.floor_eq_iff.mpr (by exact_mod_cast And.intro hl.le hu)
  have hc : ⌈x⌉ = (m : ℤ) + 1 := by
    apply Int.ceil_eq_iff.mpr
    push_cast
    constructor <;> linarith
  have hp : (m : ℤ) % 2 = 0 ↔ m % 2 = 0 := by omega
  simp only [roundEven, hf, hc, Int.cast_natCast, hp]
  split_ifs <;> simp

lemma closest_grid_iff {F : FloatFormat} {e : ℤ} {m : ℕ} {r : ℝ} {v : FVal}
    (hM : 1 ≤ F.M) (hi : GridIndex F e m) (hm : m < 2 ^ (F.M + 1))
    (hr : 0 < r) (hl : (m : ℝ) < r / 2 ^ (e - F.M))
    (hh : r / 2 ^ (e - F.M) < m + 1) :
    Closest F r ((m : ℝ) * 2 ^ (e - F.M)) (((m + 1 : ℕ) : ℝ) * 2 ^ (e - F.M)) v ↔
      v = positiveGrid F e (roundEven (r / 2 ^ (e - F.M))).toNat := by
  have hspec := positiveGrid_spec hM hi
  have hspec' := positiveGrid_spec hM (gridIndex_next hi hm)
  have hu := two_zpow_pos (e - F.M)
  have hx : r / 2 ^ (e - F.M) * 2 ^ (e - F.M) = r := div_mul_cancel₀ _ (ne_of_gt hu)
  have hl' : (m : ℝ) * 2 ^ (e - F.M) < r := (lt_div_iff₀ hu).mp hl
  have hh' : r < ((m + 1 : ℕ) : ℝ) * 2 ^ (e - F.M) := by
    simpa using (div_lt_iff₀ hu).mp hh
  rw [roundEven_toNat_between hl hh]
  simp only [Closest, abs_of_pos (sub_pos.mpr hl'), abs_of_neg (sub_neg.mpr hh'),
    hspec.2.1, hspec'.2.1, hspec.2.2 r hr v, hspec'.2.2 r hr v]
  have hlt : r - (m : ℝ) * 2 ^ (e - F.M) <
      -(r - ((m + 1 : ℕ) : ℝ) * 2 ^ (e - F.M)) ↔
      r / 2 ^ (e - F.M) - m < 1 / 2 := by push_cast; constructor <;> intro h <;> nlinarith
  have hgt : r - (m : ℝ) * 2 ^ (e - F.M) >
      -(r - ((m + 1 : ℕ) : ℝ) * 2 ^ (e - F.M)) ↔
      r / 2 ^ (e - F.M) - m > 1 / 2 := by push_cast; constructor <;> intro h <;> nlinarith
  have heq : r - (m : ℝ) * 2 ^ (e - F.M) =
      -(r - ((m + 1 : ℕ) : ℝ) * 2 ^ (e - F.M)) ↔
      r / 2 ^ (e - F.M) - m = 1 / 2 := by push_cast; constructor <;> intro h <;> nlinarith
  rw [hlt, hgt, heq]
  by_cases hlow : r / 2 ^ (e - F.M) - m < 1 / 2
  · have hhigh : ¬ r / 2 ^ (e - F.M) - m > 1 / 2 := by linarith
    have he : r / 2 ^ (e - F.M) - m ≠ 1 / 2 := ne_of_lt hlow
    simp only [hlow, hhigh, he, ↓reduceIte, true_and, false_and, or_false]
  · by_cases hhigh : r / 2 ^ (e - F.M) - m > 1 / 2
    · have he : r / 2 ^ (e - F.M) - m ≠ 1 / 2 := ne_of_gt hhigh
      simp only [hlow, hhigh, he, ↓reduceIte, true_and, false_and, false_or, or_false]
    · have he : r / 2 ^ (e - F.M) - m = 1 / 2 := by linarith
      by_cases hpar : m % 2 = 0
      · have hpar' : (m + 1) % 2 ≠ 0 := by omega
        simp [he, hpar, hpar']
      · have hpar' : (m + 1) % 2 = 0 := by omega
        simp [he, hpar, hpar']

lemma ieee_exact_rectify_iff {F : FloatFormat} {r : ℝ} {v : FVal}
    (hr : r ≠ 0) (hx : Exact F r) : Ieee F r v ↔ Rectify F r r v := by
  rcases hx with ⟨w, hw, hn, he⟩
  rw [ieee_exact_iff hw hn he hr, ← he, rectify_num_iff hw hn (by rwa [he])]

lemma ieee_at_grid_iff {F : FloatFormat} {e : ℤ} {m : ℕ} {v : FVal}
    (hM : 1 ≤ F.M) (hi : GridIndex F e m) (hm : m < 2 ^ (F.M + 1))
    (hr : 0 < (m : ℝ) * 2 ^ (e - F.M)) :
    Ieee F ((m : ℝ) * 2 ^ (e - F.M)) v ↔ v = positiveGrid F e m := by
  have hs := positiveGrid_spec hM hi
  have hlt : (m : ℝ) * 2 ^ (e - F.M) < limit F := by
    apply lt_of_lt_of_le (b := (2 : ℝ) ^ (e + 1))
    · rw [← scale_sig_succ F e]
      exact mul_lt_mul_of_pos_right (by exact_mod_cast hm) (two_zpow_pos _)
    · rw [limit_eq_zpow]
      exact zpow_le_zpow_right₀ (by norm_num) (by have := hi.upper; omega)
  have hx : Exact F ((m : ℝ) * 2 ^ (e - F.M)) := by
    rcases hs.1 with hx | hp | hn
    · exact hx
    · linarith
    · have hp := limit_pos F
      linarith
  rw [ieee_exact_rectify_iff (ne_of_gt hr) hx, hs.2.2 _ hr v]

lemma ieee_local_grid_iff {F : FloatFormat} {e : ℤ} {r : ℝ} {v : FVal}
    (hM : 1 ≤ F.M) (he : F.emin ≤ e) (he' : e ≤ F.emax) (hr : 0 < r)
    (hu : r < (2 : ℝ) ^ (e + 1)) (hl : e = F.emin ∨ (2 : ℝ) ^ e ≤ r) :
    Ieee F r v ↔ v = positiveGrid F e (roundEven (r / 2 ^ (e - F.M))).toNat := by
  let x := r / 2 ^ (e - F.M)
  let m := (⌊x⌋ : ℤ).toNat
  have hs := two_zpow_pos (e - F.M)
  have hx0 : 0 < x := div_pos hr hs
  have hm0 : 0 ≤ (⌊x⌋ : ℤ) := Int.floor_nonneg.mpr hx0.le
  have hmc : (m : ℝ) = (⌊x⌋ : ℤ) := by
    exact_mod_cast Int.toNat_of_nonneg hm0
  have hfloor : (m : ℝ) ≤ x := by rw [hmc]; exact Int.floor_le x
  have hnext : x < (m : ℝ) + 1 := by rw [hmc]; exact Int.lt_floor_add_one x
  have hxu : x < ((2 ^ (F.M + 1) : ℕ) : ℝ) := by
    apply (div_lt_iff₀ hs).mpr
    rwa [scale_sig_succ]
  have hm : m < 2 ^ (F.M + 1) := by exact_mod_cast lt_of_le_of_lt hfloor hxu
  have hi : GridIndex F e m := by
    refine ⟨he, he', hm.le, ?_⟩
    intro hsmall
    rcases hl with heq | hlow
    · exact heq
    · have hxl : ((2 ^ F.M : ℕ) : ℝ) ≤ x := by
        apply (le_div_iff₀ hs).mpr
        rwa [scale_sig]
      have hmb : 2 ^ F.M ≤ m := by
        have hbound : ((2 ^ F.M : ℕ) : ℤ) ≤ ⌊x⌋ :=
          Int.le_floor.mpr (by exact_mod_cast hxl)
        dsimp [m]
        omega
      omega
  by_cases hxe : (m : ℝ) = x
  · have hre : (m : ℝ) * 2 ^ (e - F.M) = r := (eq_div_iff (ne_of_gt hs)).mp hxe
    have hround : (roundEven x).toNat = m := by rw [← hxe, roundEven_natCast]; simp
    change Ieee F r v ↔ v = positiveGrid F e (roundEven x).toNat
    rw [hround, ← hre]
    exact ieee_at_grid_iff hM hi hm (hre.symm ▸ hr)
  · have hlow : (m : ℝ) < x := lt_of_le_of_ne hfloor hxe
    have hp := grid_adjacent hM hi hm
    have hlow' : (m : ℝ) * 2 ^ (e - F.M) < r := (lt_div_iff₀ hs).mp hlow
    have hhigh' : r < ((m + 1 : ℕ) : ℝ) * 2 ^ (e - F.M) := by
      simpa using (div_lt_iff₀ hs).mp hnext
    rw [ieee_iff_closest hp hlow' hhigh']
    exact closest_grid_iff hM hi hm hr hlow hnext

end FVA.Wasm.Num
