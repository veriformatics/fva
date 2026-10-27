import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace Verification

-- Rational Taylor polynomial for -log(1-x), and its remainder bound.
def series (x : ℚ) : ℚ :=
  ∑ i ∈ Finset.range 24, x ^ (i+1) / ((i:ℚ)+1)

def remainder (x : ℚ) : ℚ := x ^ 25 / (1-x)

theorem series_cast (x : ℚ) :
    (series x : ℝ) = ∑ i ∈ Finset.range 24, (x : ℝ) ^ (i+1) / (i+1) := by
  simp only [series, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_add,
    Rat.cast_natCast, Rat.cast_one]

theorem small_log_bound (u : ℚ) (hu : 1/2 ≤ u ∧ u ≤ 1) :
    |Real.log (u : ℝ) - (-series (1-u) : ℚ)| ≤ (remainder (1-u) : ℚ) := by
  have hu' : (1:ℝ)/2 ≤ (u:ℝ) ∧ (u:ℝ) ≤ 1 := by
    constructor
    · have hh : (((1/2:ℚ):ℝ)) ≤ (u:ℝ) := by exact_mod_cast hu.1
      norm_num at hh ⊢
      exact hh
    · exact_mod_cast hu.2
  have hx : |(1:ℝ) - u| < 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 24
  rw [abs_of_nonneg (by linarith : 0 ≤ (1:ℝ)-u)] at h
  simp only [sub_sub_cancel] at h
  have hs := series_cast (1-u)
  push_cast at hs
  rw [← hs] at h
  simpa [remainder, sub_eq_add_neg, add_comm] using h

structure LogCertificate where
  q : ℚ
  u : ℚ
  k : ℤ
  rounded : ℚ
  deriving Repr, DecidableEq

def LogCertificate.taylorCenter (c : LogCertificate) : ℚ :=
  -series (1-c.u) + c.k * (287209/414355)

def LogCertificate.taylorError (c : LogCertificate) : ℚ :=
  remainder (1-c.u) + |(c.k:ℚ)| / 10^10

def LogCertificate.valid (c : LogCertificate) : Prop :=
  (1/2 ≤ c.u ∧ c.u ≤ 1 ∧ c.q = c.u * (2:ℚ)^c.k) ∧
  |c.taylorCenter - c.rounded| + c.taylorError ≤ 1/1000000
  deriving Decidable

theorem LogCertificate.taylor_sound (c : LogCertificate) (hc : 1/2 ≤ c.u ∧ c.u ≤ 1 ∧ c.q = c.u * (2:ℚ)^c.k) :
    |Real.log (c.q : ℝ) - (c.taylorCenter : ℝ)| ≤ (c.taylorError : ℝ) := by
  have hu : (0:ℝ) < c.u := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℚ)<1/2) hc.1)
  have heq : (c.q : ℝ) = (c.u:ℝ) * (2:ℝ)^c.k := by rw [hc.2.2]; push_cast; rfl
  rw [heq, Real.log_mul (ne_of_gt hu) (zpow_ne_zero _ (by norm_num)), Real.log_zpow]
  have h1 := small_log_bound c.u ⟨hc.1, hc.2.1⟩
  have h2 := Real.log_two_near_10
  have ht := add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg (c.k:ℝ)))
  have ha := abs_add_le (Real.log (c.u:ℝ) - (-series (1-c.u):ℚ))
    ((c.k:ℝ) * (Real.log 2 - 287209/414355))
  rw [abs_mul] at ha
  unfold LogCertificate.taylorCenter LogCertificate.taylorError
  push_cast at *
  calc
    _ = |(Real.log (c.u:ℝ) - -(series (1-c.u):ℝ)) +
      (c.k:ℝ) * (Real.log 2 - 287209/414355)| := by congr 1; ring
    _ ≤ _ := ha
    _ ≤ _ := by convert ht using 1; ring

theorem LogCertificate.sound (c : LogCertificate) (hc : c.valid) :
    |Real.log (c.q : ℝ) - (c.rounded : ℝ)| ≤ (1:ℝ)/1000000 := by
  have h := c.taylor_sound hc.1
  have h' : |(c.taylorCenter:ℝ) - c.rounded| + (c.taylorError:ℝ) ≤ 1/1000000 := by
    have hh : ((|c.taylorCenter - c.rounded| + c.taylorError:ℚ):ℝ) ≤ ((1/1000000:ℚ):ℝ) := by
      exact_mod_cast hc.2
    push_cast at hh
    exact hh
  have ha := abs_add_le (Real.log (c.q:ℝ) - (c.taylorCenter:ℝ))
    ((c.taylorCenter:ℝ) - c.rounded)
  rw [sub_add_sub_cancel] at ha
  linarith

abbrev Form := List (ℚ × LogCertificate)
noncomputable def value (f : Form) : ℝ :=
  (f.map fun (w,c) => (w:ℝ) * Real.log (c.q:ℝ)).sum

def center (f : Form) : ℚ := (f.map fun (w,c) => w*c.rounded).sum
def error (f : Form) : ℚ := (f.map fun t => |t.1| / 1000000).sum

theorem form_sound (f : Form) (hf : ∀ t ∈ f, t.2.valid) :
    |value f - (center f : ℝ)| ≤ (error f : ℝ) := by
  induction f with
  | nil => simp [value, center, error]
  | cons t ts ih =>
    obtain ⟨w,c⟩ := t
    have ht := c.sound (hf (w,c) (by simp))
    have hs := ih (fun t h => hf t (by simp [h]))
    have hw := mul_le_mul_of_nonneg_left ht (abs_nonneg (w:ℝ))
    have ha := abs_add_le ((w:ℝ)*(Real.log (c.q:ℝ) - (c.rounded:ℝ)))
      (value ts - (center ts:ℝ))
    rw [abs_mul] at ha
    change |(w:ℝ)*Real.log (c.q:ℝ) + value ts - ((w*c.rounded + center ts:ℚ):ℝ)| ≤
      ((|w| / 1000000 + error ts:ℚ):ℝ)
    push_cast
    calc
      _ = |(w:ℝ)*(Real.log (c.q:ℝ) - (c.rounded:ℝ)) +
        (value ts - (center ts:ℝ))| := by congr 1; ring
      _ ≤ _ := ha
      _ ≤ _ := by convert add_le_add hw hs using 1; ring

end Verification
