import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/- Rational certificates for real logarithms. No floating-point operations are used here. -/
namespace Verification

def logSeries (z : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, z ^ (2*i+1) / (2*i+1 : ℕ)

def logError (z : ℚ) (n : ℕ) : ℚ := |z| ^ (2*n+1) / (1-z^2)

def LogCheck (q l u : ℚ) (n : ℕ) : Prop :=
  0 < q ∧ |(q-1)/(q+1)| < 1 ∧
  l ≤ 2 * logSeries ((q-1)/(q+1)) n - 2 * logError ((q-1)/(q+1)) n ∧
  2 * logSeries ((q-1)/(q+1)) n + 2 * logError ((q-1)/(q+1)) n ≤ u
instance (q l u : ℚ) (n : ℕ) : Decidable (LogCheck q l u n) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

lemma cast_series (z : ℚ) (n : ℕ) :
    (logSeries z n : ℝ) = ∑ i ∈ Finset.range n, (z : ℝ) ^ (2*i+1) / (2*i+1 : ℕ) := by
  simp [logSeries]

lemma log_check_sound (q l u : ℚ) (n : ℕ) (h : LogCheck q l u n) :
    (l : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ (u : ℝ) := by
  rcases h with ⟨hq, hz, hl, hu⟩
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hz' : |((q : ℝ)-1)/(q+1)| < 1 := by exact_mod_cast hz
  have heq : (1 + ((q : ℝ)-1)/(q+1))/(1-((q : ℝ)-1)/(q+1)) = q := by
    field_simp
    ring
  have hs := Real.sum_range_sub_log_div_le hz' n
  rw [heq] at hs
  have hs' : |1/2 * Real.log (q : ℝ) - (logSeries ((q-1)/(q+1)) n : ℝ)| ≤
      (logError ((q-1)/(q+1)) n : ℝ) := by
    simpa [cast_series, logError] using hs
  have hl' : (l : ℝ) ≤ 2 * (logSeries ((q-1)/(q+1)) n : ℝ) -
      2 * (logError ((q-1)/(q+1)) n : ℝ) := by exact_mod_cast hl
  have hu' : 2 * (logSeries ((q-1)/(q+1)) n : ℝ) +
      2 * (logError ((q-1)/(q+1)) n : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  rcases abs_le.mp hs' with ⟨h₁,h₂⟩
  constructor <;> linarith

end Verification

namespace Verification

/-- A rational interval with a kernel-checked proof that it contains log(q). -/
structure LogBounds where
  q : ℚ
  positive : 0 < q
  lo : ℚ
  hi : ℚ
  sound : (lo : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ (hi : ℝ)

abbrev Term := ℚ × LogBounds

noncomputable def value (ts : List Term) : ℝ :=
  (ts.map fun t => (t.1 : ℝ) * Real.log (t.2.q : ℝ)).sum

def lower (ts : List Term) : ℚ :=
  (ts.map fun t => t.1 * (if 0 ≤ t.1 then t.2.lo else t.2.hi)).sum

def upper (ts : List Term) : ℚ :=
  (ts.map fun t => t.1 * (if 0 ≤ t.1 then t.2.hi else t.2.lo)).sum

lemma term_bounds (t : Term) :
    ((t.1 * (if 0 ≤ t.1 then t.2.lo else t.2.hi) : ℚ) : ℝ) ≤
      (t.1 : ℝ) * Real.log (t.2.q : ℝ) ∧
    (t.1 : ℝ) * Real.log (t.2.q : ℝ) ≤
      ((t.1 * (if 0 ≤ t.1 then t.2.hi else t.2.lo) : ℚ) : ℝ) := by
  rcases t.2.sound with ⟨hl,hu⟩
  split_ifs with h
  · have h' : (0 : ℝ) ≤ t.1 := by exact_mod_cast h
    push_cast
    exact ⟨mul_le_mul_of_nonneg_left hl h', mul_le_mul_of_nonneg_left hu h'⟩
  · have h' : (t.1 : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge h))
    push_cast
    exact ⟨mul_le_mul_of_nonpos_left hu h', mul_le_mul_of_nonpos_left hl h'⟩

lemma value_bounds (ts : List Term) : (lower ts : ℝ) ≤ value ts ∧ value ts ≤ (upper ts : ℝ) := by
  induction ts with
  | nil => simp [lower,upper,value]
  | cons t ts ih =>
    have ht := term_bounds t
    simp only [lower,upper,value,List.map_cons,List.sum_cons,Rat.cast_add] at *
    constructor <;> linarith [ht.1,ht.2,ih.1,ih.2]

end Verification

namespace Verification
lemma value_between (ts : List Term) (l u : ℚ)
    (hl : l ≤ lower ts) (hu : upper ts ≤ u) :
    (l : ℝ) ≤ value ts ∧ value ts ≤ (u : ℝ) := by
  have h := value_bounds ts
  have hl' : (l : ℝ) ≤ (lower ts : ℝ) := by exact_mod_cast hl
  have hu' : (upper ts : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  exact ⟨le_trans hl' h.1, le_trans h.2 hu'⟩

/-- Geometric-mean normalization in natural-log coordinates. -/
noncomputable def factor (raw : Fin 7 → ℝ) (i : Fin 7) : ℝ :=
  Real.exp (raw i - (∑ j, raw j) / 7)

lemma factor_between (raw : Fin 7 → ℝ) (lo hi : Fin 7 → ℚ)
    (h : ∀ i, (lo i : ℝ) ≤ raw i ∧ raw i ≤ (hi i : ℝ))
    (i : Fin 7) (l u : LogBounds)
    (hl : l.hi ≤ lo i - (∑ j, hi j) / 7)
    (hu : hi i - (∑ j, lo j) / 7 ≤ u.lo) :
    (l.q : ℝ) ≤ factor raw i ∧ factor raw i ≤ (u.q : ℝ) := by
  have sumlo : (∑ j, (lo j : ℝ)) ≤ ∑ j, raw j :=
    Finset.sum_le_sum fun j _ => (h j).1
  have sumhi : (∑ j, raw j) ≤ ∑ j, (hi j : ℝ) :=
    Finset.sum_le_sum fun j _ => (h j).2
  have hl' : (l.hi : ℝ) ≤ (lo i : ℝ) - (∑ j, (hi j : ℝ)) / 7 := by exact_mod_cast hl
  have hu' : (hi i : ℝ) - (∑ j, (lo j : ℝ)) / 7 ≤ (u.lo : ℝ) := by exact_mod_cast hu
  have h₁ : Real.log (l.q : ℝ) ≤ raw i - (∑ j, raw j) / 7 := by
    linarith [l.sound.2, (h i).1]
  have h₂ : raw i - (∑ j, raw j) / 7 ≤ Real.log (u.q : ℝ) := by
    linarith [u.sound.1, (h i).2]
  constructor
  · have lp : (0 : ℝ) < l.q := by exact_mod_cast l.positive
    simpa [factor, Real.exp_log lp] using Real.exp_le_exp.mpr h₁
  · have up : (0 : ℝ) < u.q := by exact_mod_cast u.positive
    simpa [factor, Real.exp_log up] using Real.exp_le_exp.mpr h₂

lemma factor_near (raw : Fin 7 → ℝ) (lo hi : Fin 7 → ℚ)
    (h : ∀ i, (lo i : ℝ) ≤ raw i ∧ raw i ≤ (hi i : ℝ))
    (i : Fin 7) (l u : LogBounds) (f eps : ℚ)
    (hl : l.hi ≤ lo i - (∑ j, hi j) / 7)
    (hu : hi i - (∑ j, lo j) / 7 ≤ u.lo)
    (hlq : l.q = f - eps) (huq : u.q = f + eps) :
    |factor raw i - (f : ℝ)| ≤ (eps : ℝ) := by
  have hb := factor_between raw lo hi h i l u hl hu
  rw [hlq, huq] at hb
  push_cast at hb
  exact abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩
end Verification
