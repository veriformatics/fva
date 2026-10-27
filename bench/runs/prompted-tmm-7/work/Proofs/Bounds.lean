import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace Verify

-- Four terms of atanh; the remainder bound is proved in Mathlib.
def z (q : ℚ) : ℚ := (q - 1) / (q + 1)
def poly (t : ℚ) : ℚ := t + t^3/3 + t^5/5 + t^7/7
def err (t : ℚ) : ℚ := |t|^9 / (1 - t^2)
def logLo (q : ℚ) : ℚ := 2 * (poly (z q) - err (z q))
def logHi (q : ℚ) : ℚ := 2 * (poly (z q) + err (z q))

theorem log_bounds (q : ℚ) (hq : 0 < q) (hz : |z q| < 1) :
    (logLo q : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ (logHi q : ℝ) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hz' : |((z q : ℚ) : ℝ)| < 1 := by exact_mod_cast hz
  have hid : (1 + ((z q : ℚ) : ℝ)) / (1 - ((z q : ℚ) : ℝ)) = (q : ℝ) := by
    simp only [z, Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_one]
    field_simp
    nlinarith
  have h := Real.sum_range_sub_log_div_le hz' 4
  rw [hid] at h
  have he : ((err (z q) : ℚ) : ℝ) = |((z q : ℚ) : ℝ)|^9 / (1 - ((z q : ℚ) : ℝ)^2) := by
    simp [err]
  have hp : ((poly (z q) : ℚ) : ℝ) =
      ∑ i ∈ Finset.range 4, ((z q : ℚ) : ℝ) ^ (2 * i + 1) / (2 * i + 1) := by
    norm_num [poly, Finset.sum_range_succ]
  rw [← he, ← hp] at h
  have hh := abs_le.mp h
  constructor <;> push_cast [logLo, logHi] <;> linarith [hh.1, hh.2]

abbrev Term := ℚ × ℚ -- ratio, inverse variance (including multiplicity)
abbrev Cert := ℚ × ℚ -- rounded contributions relative to two target bounds

def leaf (t : Term) (a b : ℚ) (c : Cert) : Prop :=
  0 < t.1 ∧ 0 ≤ t.2 ∧ |z t.1| < 1 ∧
  c.1 ≤ t.2 * (logLo t.1 - a) ∧ t.2 * (logHi t.1 - b) ≤ c.2

def leaves : List Term → ℚ → ℚ → List Cert → Prop
  | [], _, _, [] => True
  | t::ts, a, b, c::cs => leaf t a b c ∧ leaves ts a b cs
  | _, _, _, _ => False

instance (t : Term) (a b : ℚ) (c : Cert) : Decidable (leaf t a b c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))
instance (ts : List Term) (a b : ℚ) (cs : List Cert) : Decidable (leaves ts a b cs) := by
  induction ts generalizing cs with
  | nil => cases cs <;> simp [leaves] <;> infer_instance
  | cons t ts ih => cases cs <;> simp only [leaves]; infer_instance; exact instDecidableAnd

def weight (ts : List Term) : ℚ := (ts.map Prod.snd).sum
noncomputable def weightedLog (ts : List Term) : ℝ :=
  (ts.map fun t => (t.2 : ℝ) * Real.log (t.1 : ℝ)).sum
noncomputable def meanLog (ts : List Term) : ℝ := weightedLog ts / (weight ts : ℝ)

theorem sum_bounds (ts : List Term) (cs : List Cert) (a b : ℚ)
    (h : leaves ts a b cs) :
    ((cs.map Prod.fst).sum : ℚ) ≤ weightedLog ts - (a : ℝ) * (weight ts : ℝ) ∧
    weightedLog ts - (b : ℝ) * (weight ts : ℝ) ≤ ((cs.map Prod.snd).sum : ℚ) := by
  induction ts generalizing cs with
  | nil => cases cs <;> simp_all [leaves, weightedLog, weight]
  | cons t ts ih =>
    cases cs with
    | nil => simp [leaves] at h
    | cons c cs =>
      obtain ⟨ht, hs⟩ := h
      obtain ⟨hq, hw, hz, hl, hu⟩ := ht
      have hb := log_bounds t.1 hq hz
      have hw' : (0 : ℝ) ≤ t.2 := by exact_mod_cast hw
      have hl' : (c.1 : ℝ) ≤ (t.2 : ℝ) * ((logLo t.1 : ℝ) - (a : ℝ)) := by exact_mod_cast hl
      have hu' : (t.2 : ℝ) * ((logHi t.1 : ℝ) - (b : ℝ)) ≤ (c.2 : ℝ) := by exact_mod_cast hu
      have hll := mul_le_mul_of_nonneg_left hb.1 hw'
      have huu := mul_le_mul_of_nonneg_left hb.2 hw'
      have hi := ih cs hs
      simp only [weightedLog, weight, List.map_cons, List.sum_cons, Rat.cast_add] at *
      constructor <;> nlinarith [hi.1, hi.2]

theorem mean_bounds (ts : List Term) (cs : List Cert) (a b : ℚ)
    (h : leaves ts a b cs) (hw : 0 < weight ts)
    (hl : 0 ≤ (cs.map Prod.fst).sum) (hu : (cs.map Prod.snd).sum ≤ 0) :
    (a : ℝ) ≤ meanLog ts ∧ meanLog ts ≤ (b : ℝ) := by
  have hw' : (0 : ℝ) < weight ts := by exact_mod_cast hw
  have hl' : (0 : ℝ) ≤ ((cs.map Prod.fst).sum : ℚ) := by exact_mod_cast hl
  have hu' : (((cs.map Prod.snd).sum : ℚ) : ℝ) ≤ 0 := by exact_mod_cast hu
  obtain ⟨hlb, hub⟩ := sum_bounds ts cs a b h
  unfold meanLog
  constructor
  · apply (le_div_iff₀ hw').mpr
    linarith
  · apply (div_le_iff₀ hw').mpr
    linarith
end Verify
