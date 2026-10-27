import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace TMM

structure Box where
  lo : ℚ
  hi : ℚ
  deriving Repr, DecidableEq

def Box.Holds (b : Box) (x : ℝ) : Prop := (b.lo : ℝ) ≤ x ∧ x ≤ (b.hi : ℝ)
def Box.point (q : ℚ) : Box := ⟨q, q⟩
def Box.add (a b : Box) : Box := ⟨a.lo + b.lo, a.hi + b.hi⟩
def Box.neg (a : Box) : Box := ⟨-a.hi, -a.lo⟩
def Box.scale (q : ℚ) (a : Box) : Box := ⟨q * a.lo, q * a.hi⟩

lemma point_sound (q : ℚ) : (Box.point q).Holds (q : ℝ) := ⟨le_rfl, le_rfl⟩
lemma add_sound {a b : Box} {x y : ℝ} (ha : a.Holds x) (hb : b.Holds y) :
    (a.add b).Holds (x + y) := by
  simp only [Box.Holds, Box.add, Rat.cast_add]
  exact ⟨add_le_add ha.1 hb.1, add_le_add ha.2 hb.2⟩
lemma neg_sound {a : Box} {x : ℝ} (ha : a.Holds x) : a.neg.Holds (-x) := by
  simp only [Box.Holds, Box.neg, Rat.cast_neg]
  exact ⟨neg_le_neg ha.2, neg_le_neg ha.1⟩
lemma scale_sound {a : Box} {x : ℝ} (q : ℚ) (hq : 0 ≤ q) (ha : a.Holds x) :
    (a.scale q).Holds ((q : ℝ) * x) := by
  simp only [Box.Holds, Box.scale, Rat.cast_mul]
  have h : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  exact ⟨mul_le_mul_of_nonneg_left ha.1 h, mul_le_mul_of_nonneg_left ha.2 h⟩

/-- Twelve-term atanh expansion, evaluated over exact rationals. -/
def logSeries (q : ℚ) : ℚ :=
  2 * (Finset.range 12).sum (fun i => ((q - 1) / (q + 1)) ^ (2*i+1) / (2*i+1))
def logError (q : ℚ) : ℚ :=
  2 * ((q - 1) / (q + 1)) ^ 25 / (1 - ((q - 1) / (q + 1)) ^ 2)
def baseLog (q : ℚ) : Box := ⟨logSeries q, logSeries q + logError q⟩

lemma baseLog_sound (q : ℚ) (h1 : 1 ≤ q) (h2 : q ≤ 2) :
    (baseLog q).Holds (Real.log (q : ℝ)) := by
  have h1r : (1 : ℝ) ≤ q := by exact_mod_cast h1
  have h2r : (q : ℝ) ≤ 2 := by exact_mod_cast h2
  let x : ℝ := ((q : ℝ) - 1) / ((q : ℝ) + 1)
  have hx0 : 0 ≤ x := div_nonneg (by linarith) (by linarith)
  have hx1 : x < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hid : (1 + x) / (1 - x) = (q : ℝ) := by
    dsimp [x]
    field_simp; ring
  have hl := Real.sum_range_le_log_div hx0 hx1 12
  have hu := Real.log_div_le_sum_range_add hx0 hx1 12
  rw [hid] at hl hu
  have hs : (logSeries q : ℝ) =
      2 * (Finset.range 12).sum (fun i => x ^ (2*i+1) / (2*i+1)) := by
    simp [logSeries, x]
  have he : (logError q : ℝ) = 2 * x ^ 25 / (1 - x ^ 2) := by
    simp [logError, x]
  simp only [Box.Holds, baseLog, Rat.cast_add]
  rw [hs, he]
  norm_num only [Nat.reduceMul, Nat.reduceAdd] at hu
  rw [mul_div_assoc]
  constructor <;> linarith

/-- Fuel bounds the number of exact range reductions. Validity is checked separately. -/
def logBox : Nat → ℚ → Box
  | 0, q => baseLog q
  | n+1, q =>
    if q < 1 then (logBox n (1/q)).neg
    else if 2 < q then (logBox n (q/2)).add (baseLog 2)
    else baseLog q

def logValid : Nat → ℚ → Bool
  | 0, q => decide (1 ≤ q ∧ q ≤ 2)
  | n+1, q =>
    if q < 1 then decide (0 < q) && logValid n (1/q)
    else if 2 < q then logValid n (q/2)
    else decide (1 ≤ q ∧ q ≤ 2)

lemma logBox_sound (n : Nat) (q : ℚ) (h : logValid n q = true) :
    (logBox n q).Holds (Real.log (q : ℝ)) := by
  induction n generalizing q with
  | zero =>
    simp only [logValid, decide_eq_true_eq] at h
    exact baseLog_sound q h.1 h.2
  | succ n ih =>
    simp only [logBox]
    split_ifs with hsmall hlarge
    · simp only [logValid, ite_eq_left hsmall, Bool.and_eq_true, decide_eq_true_eq] at h
      have hn := neg_sound (ih (1/q) h.2)
      simpa [Real.log_inv] using hn
    · simp only [logValid, ite_eq_right hsmall, ite_eq_left hlarge] at h
      have hn := add_sound (ih (q/2) h) (baseLog_sound 2 (by norm_num) (by norm_num))
      norm_num only [Rat.cast_ofNat] at hn
      have heq : Real.log ((q/2 : ℚ) : ℝ) + Real.log (2 : ℝ) = Real.log (q : ℝ) := by
        rw [← Real.log_mul (by positivity) (by norm_num)]
        congr 1
        push_cast
        ring
      rwa [heq] at hn
    · simp only [logValid, ite_eq_right hsmall, ite_eq_right hlarge, decide_eq_true_eq] at h
      exact baseLog_sound q h.1 h.2

/-- Taylor enclosure for exp on [-1,1]. -/
def expSeries (q : ℚ) : ℚ :=
  (Finset.range 12).sum (fun i => q ^ i / (i.factorial : ℚ))
def expError (q : ℚ) : ℚ := |q| ^ 12 * (13 / ((12 : Nat).factorial * 12 : ℚ))
def expBox (q : ℚ) : Box := ⟨expSeries q - expError q, expSeries q + expError q⟩

lemma expBox_sound (q : ℚ) (h : |q| ≤ 1) : (expBox q).Holds (Real.exp (q : ℝ)) := by
  have hr : |(q : ℝ)| ≤ 1 := by exact_mod_cast h
  have hb := Real.exp_bound (n := 12) hr (by norm_num)
  have hs : (expSeries q : ℝ) =
      (Finset.range 12).sum (fun i => (q : ℝ) ^ i / (i.factorial : ℝ)) := by
    simp [expSeries]
  have he : (expError q : ℝ) = |(q : ℝ)| ^ 12 * (13 / ((12 : Nat).factorial * 12 : ℝ)) := by
    simp [expError]
  simp only [Box.Holds, expBox, Rat.cast_sub, Rat.cast_add]
  rw [hs, he]
  have hb' := abs_le.mp hb
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hb'
  constructor <;> linarith

lemma exp_interval_sound {b : Box} {x : ℝ} (h : b.Holds x)
    (hl : |b.lo| ≤ 1) (hu : |b.hi| ≤ 1) :
    (⟨(expBox b.lo).lo, (expBox b.hi).hi⟩ : Box).Holds (Real.exp x) := by
  exact ⟨(expBox_sound b.lo hl).1.trans (Real.exp_le_exp.mpr h.1),
    (Real.exp_le_exp.mpr h.2).trans (expBox_sound b.hi hu).2⟩

end TMM
