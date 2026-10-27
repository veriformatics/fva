import Proofs.Model
import Mathlib.Tactic

namespace Proofs.Bounds
open Proofs.Model

def z (q : ℚ) : ℚ := (q - 1) / (q + 1)
def approx (q : ℚ) : ℚ :=
  2 * (Finset.range 4).sum (fun i => z q ^ (2 * i + 1) / (2 * i + 1 : Nat))
def error (q : ℚ) : ℚ := 2 * |z q| ^ 9 / (1 - z q ^ 2)
def lo (q : ℚ) : ℚ := approx q - error q
def hi (q : ℚ) : ℚ := approx q + error q

theorem log_bounds (q : ℚ) (hq : 0 < q) :
    (lo q : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ (hi q : ℝ) := by
  have hp : (0 : ℝ) < q := by exact_mod_cast hq
  have hd : (q : ℝ) + 1 > 0 := by linarith
  have hz : |((q : ℝ) - 1) / ((q : ℝ) + 1)| < 1 := by
    rw [abs_lt]
    constructor
    · apply (lt_div_iff₀ hd).2; linarith
    · apply (div_lt_iff₀ hd).2; linarith
  have heq : (1 + ((q : ℝ) - 1) / ((q : ℝ) + 1)) /
      (1 - ((q : ℝ) - 1) / ((q : ℝ) + 1)) = q := by
    field_simp
    ring
  have h := Real.sum_range_sub_log_div_le hz 4
  rw [heq] at h
  have hh := abs_le.mp h
  dsimp [lo, hi, approx, error, z]
  push_cast
  norm_num at hh ⊢
  simp only [mul_div_assoc]
  constructor <;> linarith only [hh.1, hh.2]

def weight (es : List (ℚ × ℚ)) : ℚ := (es.map Prod.snd).sum
def lower (es : List (ℚ × ℚ)) : ℚ :=
  (es.map fun p => p.2 * lo p.1).sum / weight es
def upper (es : List (ℚ × ℚ)) : ℚ :=
  (es.map fun p => p.2 * hi p.1).sum / weight es

def good (es : List (ℚ × ℚ)) : Prop :=
  (∀ p ∈ es, 0 < p.1 ∧ 0 ≤ p.2) ∧ 0 < weight es

instance (es : List (ℚ × ℚ)) : Decidable (good es) := by
  unfold good
  infer_instance

theorem weighted_bounds (es : List (ℚ × ℚ)) (hg : good es) :
    (lower es : ℝ) ≤ score es ∧ score es ≤ (upper es : ℝ) := by
  have hsum :
      ((es.map fun p => p.2 * lo p.1).sum : ℝ) ≤
        (es.map fun p => (p.2 : ℝ) * Real.log (p.1 : ℝ)).sum ∧
      (es.map fun p => (p.2 : ℝ) * Real.log (p.1 : ℝ)).sum ≤
        ((es.map fun p => p.2 * hi p.1).sum : ℝ) := by
    have hgood := hg.1
    clear hg
    induction es with
    | nil => simp
    | cons p ps ih =>
      have hp := hgood p (by simp)
      have ih' := ih (fun p h => hgood p (by simp [h]))
      have hb := log_bounds p.1 hp.1
      have hw : (0 : ℝ) ≤ p.2 := by exact_mod_cast hp.2
      simp only [List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul]
      constructor
      · exact add_le_add (mul_le_mul_of_nonneg_left hb.1 hw) ih'.1
      · exact add_le_add (mul_le_mul_of_nonneg_left hb.2 hw) ih'.2
  have hw : (0 : ℝ) < weight es := by exact_mod_cast hg.2
  dsimp [lower, upper, score]
  simp only [Rat.cast_div]
  exact ⟨div_le_div_of_nonneg_right hsum.1 hw.le,
    div_le_div_of_nonneg_right hsum.2 hw.le⟩

def centerLo (bs : List (ℚ × ℚ)) (b : ℚ × ℚ) : ℚ :=
  b.1 - (bs.map Prod.snd).sum / (bs.length : ℚ)
def centerHi (bs : List (ℚ × ℚ)) (b : ℚ × ℚ) : ℚ :=
  b.2 - (bs.map Prod.fst).sum / (bs.length : ℚ)

def Fits (eps : ℚ) (bs : List (ℚ × ℚ)) (ys : List ℚ) : Prop :=
  List.Forall₂ (fun y b => 0 < y - eps ∧ 0 < y + eps ∧
    hi (y - eps) ≤ centerLo bs b ∧ centerHi bs b ≤ lo (y + eps)) ys bs

theorem sum_bounds {ss : List ℝ} {bs : List (ℚ × ℚ)}
    (h : List.Forall₂ (fun s b => (b.1 : ℝ) ≤ s ∧ s ≤ (b.2 : ℝ)) ss bs) :
    ((bs.map Prod.fst).sum : ℝ) ≤ ss.sum ∧ ss.sum ≤ ((bs.map Prod.snd).sum : ℝ) := by
  induction h with
  | nil => simp
  | @cons s b ss bs h hs ih =>
    simp only [List.map_cons, List.sum_cons, Rat.cast_add]
    exact ⟨add_le_add h.1 ih.1, add_le_add h.2 ih.2⟩

theorem exp_close (y eps a b : ℚ)
    (x : ℝ) (hp : 0 < y - eps) (hp' : 0 < y + eps)
    (ha : hi (y - eps) ≤ a) (hb : b ≤ lo (y + eps))
    (hx : (a : ℝ) ≤ x ∧ x ≤ (b : ℝ)) :
    |(y : ℝ) - Real.exp x| ≤ (eps : ℝ) := by
  have hl := (log_bounds (y - eps) hp).2
  have hu := (log_bounds (y + eps) hp').1
  have ha' : (hi (y - eps) : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (b : ℝ) ≤ lo (y + eps) := by exact_mod_cast hb
  have hl' : Real.log ((y : ℝ) - eps) ≤ x := by
    push_cast at hl
    exact hl.trans (ha'.trans hx.1)
  have hu' : x ≤ Real.log ((y : ℝ) + eps) := by
    push_cast at hu
    exact hx.2.trans (hb'.trans hu)
  have hpR : (0 : ℝ) < (y : ℝ) - eps := by exact_mod_cast hp
  have hpR' : (0 : ℝ) < (y : ℝ) + eps := by exact_mod_cast hp'
  have h1 := Real.exp_le_exp.mpr hl'
  have h2 := Real.exp_le_exp.mpr hu'
  rw [Real.exp_log hpR] at h1
  rw [Real.exp_log hpR'] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem accurate_of_bounds (input output : List UInt8) (eps : ℚ)
    (bs : List (ℚ × ℚ))
    (hcount : (factors output).length = 7)
    (hbs : bs.length = 7)
    (hs : List.Forall₂
      (fun es b => good es ∧ b.1 ≤ lower es ∧ upper es ≤ b.2)
      (samples input) bs)
    (hf : Fits eps bs (factors output)) : Accurate eps input output := by
  have h : List.Forall₂ (fun s b => (b.1 : ℝ) ≤ s ∧ s ≤ (b.2 : ℝ))
      ((samples input).map score) bs := by
    apply List.forall₂_map_left_iff.mpr
    apply hs.imp
    intro es b hb
    have hw := weighted_bounds es hb.1
    have h1 : (b.1 : ℝ) ≤ lower es := by exact_mod_cast hb.2.1
    have h2 : (upper es : ℝ) ≤ b.2 := by exact_mod_cast hb.2.2
    exact ⟨h1.trans hw.1, hw.2.trans h2⟩
  have hlen := h.length_eq
  have hn : ((samples input).map score).length = 7 := hlen.trans hbs
  have htmm : (tmm input).length = 7 := by simp only [tmm, List.length_map]; simpa using hn
  refine ⟨hcount, htmm, ?_⟩
  have hsum := sum_bounds h
  have hden : (0 : ℝ) < bs.length := by rw [hbs]; norm_num
  have hc : List.Forall₂
      (fun s b => (centerLo bs b : ℝ) ≤ s ∧ s ≤ (centerHi bs b : ℝ))
      (((samples input).map score).map
        (fun s => s - ((samples input).map score).sum /
          (((samples input).map score).length : ℝ))) bs := by
    apply List.forall₂_map_left_iff.mpr
    apply h.imp
    intro s b hb
    dsimp [centerLo, centerHi]
    simp only [Rat.cast_sub, Rat.cast_div, Rat.cast_natCast]
    rw [hlen]
    constructor
    · exact sub_le_sub hb.1 (div_le_div_of_nonneg_right hsum.2 hden.le)
    · exact sub_le_sub hb.2 (div_le_div_of_nonneg_right hsum.1 hden.le)
  unfold Fits at hf
  have join : ∀ (ys : List ℚ) (ss : List ℝ) (bs' : List (ℚ × ℚ)),
      List.Forall₂ (fun y b => 0 < y - eps ∧ 0 < y + eps ∧
        hi (y - eps) ≤ centerLo bs b ∧ centerHi bs b ≤ lo (y + eps)) ys bs' →
      List.Forall₂ (fun s b => (centerLo bs b : ℝ) ≤ s ∧ s ≤ (centerHi bs b : ℝ)) ss bs' →
      List.Forall₂ (fun (y : ℚ) s => |(y : ℝ) - Real.exp s| ≤ (eps : ℝ)) ys ss := by
    intro ys ss bs' hfit
    induction hfit generalizing ss with
    | nil => intro hh; cases hh; exact .nil
    | @cons y b ys bs' hy hf ih =>
      intro hh
      cases hh with
      | cons hx hrest =>
        exact .cons (exp_close y eps (centerLo bs b) (centerHi bs b) _
          hy.1 hy.2.1 hy.2.2.1 hy.2.2.2 hx) (ih _ hrest)
  have hh := join _ _ _ hf hc
  simpa only [List.forall₂_map_right_iff, tmm] using hh

end Proofs.Bounds
