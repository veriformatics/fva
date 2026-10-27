import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace TMM
structure Box where
  lo : ℚ
  hi : ℚ
  deriving Repr, DecidableEq

def Box.Holds (a : Box) (x : ℝ) : Prop := (a.lo : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ)
def Box.point (q : ℚ) : Box := ⟨q,q⟩
def Box.add (a b : Box) : Box := ⟨a.lo+b.lo,a.hi+b.hi⟩
def Box.sub (a b : Box) : Box := ⟨a.lo-b.hi,a.hi-b.lo⟩
def Box.mul (a b : Box) : Box :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩
def Box.inv (a : Box) : Box := ⟨1/a.hi,1/a.lo⟩
def Box.div (a b : Box) : Box := a.mul b.inv

theorem point_sound (q : ℚ) : (Box.point q).Holds (q : ℝ) := ⟨le_rfl,le_rfl⟩
theorem add_sound {a b : Box} {x y : ℝ} (hx : a.Holds x) (hy : b.Holds y) :
    (a.add b).Holds (x+y) := by
  rcases hx with ⟨hx,hx'⟩; rcases hy with ⟨hy,hy'⟩
  simp only [Box.Holds,Box.add,Rat.cast_add]
  constructor <;> linarith

theorem sub_sound {a b : Box} {x y : ℝ} (hx : a.Holds x) (hy : b.Holds y) :
    (a.sub b).Holds (x-y) := by
  rcases hx with ⟨hx,hx'⟩; rcases hy with ⟨hy,hy'⟩
  simp only [Box.Holds,Box.sub,Rat.cast_sub]
  constructor <;> linarith

private theorem mul_range {a b c d x y : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
    x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  constructor
  · rcases le_total 0 x with h | h
    · have hxy : x*c ≤ x*y := mul_le_mul_of_nonneg_left hy.1 h
      rcases le_total 0 c with k | k
      · exact (min_le_of_left_le (min_le_left _ _)).trans ((mul_le_mul_of_nonneg_right hx.1 k).trans hxy)
      · exact (min_le_of_right_le (min_le_left _ _)).trans ((mul_le_mul_of_nonpos_right hx.2 k).trans hxy)
    · have hxy : x*d ≤ x*y := mul_le_mul_of_nonpos_left hy.2 h
      rcases le_total 0 d with k | k
      · exact (min_le_of_left_le (min_le_right _ _)).trans ((mul_le_mul_of_nonneg_right hx.1 k).trans hxy)
      · exact (min_le_of_right_le (min_le_right _ _)).trans ((mul_le_mul_of_nonpos_right hx.2 k).trans hxy)
  · rcases le_total 0 x with h | h
    · have hxy : x*y ≤ x*d := mul_le_mul_of_nonneg_left hy.2 h
      rcases le_total 0 d with k | k
      · exact (hxy.trans (mul_le_mul_of_nonneg_right hx.2 k)).trans (le_max_of_le_right (le_max_right _ _))
      · exact (hxy.trans (mul_le_mul_of_nonpos_right hx.1 k)).trans (le_max_of_le_left (le_max_right _ _))
    · have hxy : x*y ≤ x*c := mul_le_mul_of_nonpos_left hy.1 h
      rcases le_total 0 c with k | k
      · exact (hxy.trans (mul_le_mul_of_nonneg_right hx.2 k)).trans (le_max_of_le_right (le_max_left _ _))
      · exact (hxy.trans (mul_le_mul_of_nonpos_right hx.1 k)).trans (le_max_of_le_left (le_max_left _ _))

theorem mul_sound {a b : Box} {x y : ℝ} (hx : a.Holds x) (hy : b.Holds y) :
    (a.mul b).Holds (x*y) := by
  simpa only [Box.Holds,Box.mul,Rat.cast_min,Rat.cast_max,Rat.cast_mul] using mul_range hx hy

theorem inv_sound {a : Box} {x : ℝ} (hx : a.Holds x) (hp : 0 < a.lo) :
    a.inv.Holds (1/x) := by
  have hp' : (0:ℝ) < a.lo := by exact_mod_cast hp
  have hxp : 0 < x := hp'.trans_le hx.1
  simpa only [Box.Holds,Box.inv,Rat.cast_div,Rat.cast_one] using
    And.intro (one_div_le_one_div_of_le hxp hx.2) (one_div_le_one_div_of_le hp' hx.1)

theorem div_sound {a b : Box} {x y : ℝ} (hx : a.Holds x) (hy : b.Holds y)
    (hp : 0 < b.lo) : (a.div b).Holds (x/y) := by
  have he : x/y = x*(1/y) := by ring
  rw [he]
  exact mul_sound hx (inv_sound hy hp)

def series (z : ℚ) (n : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range n, z^(2*i+1) / (2*i+1)
def tail (z : ℚ) (n : ℕ) : ℚ := 2*(z^(2*n+1)/(1-z^2))

theorem log_series_bound (z : ℚ) (n : ℕ) (hz : 0 ≤ z) (hz' : z < 1) :
    (⟨series z n, series z n + tail z n⟩ : Box).Holds
      (Real.log (((1+z)/(1-z) : ℚ) : ℝ)) := by
  have h0 : (0:ℝ) ≤ z := by exact_mod_cast hz
  have h1 : (z:ℝ) < 1 := by exact_mod_cast hz'
  have a := Real.sum_range_le_log_div h0 h1 n
  have b := Real.log_div_le_sum_range_add h0 h1 n
  simp only [Box.Holds,series,tail,Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat,
    Rat.cast_sum,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_sub,Rat.cast_one]
  constructor
  · linarith
  · linarith only [b]

-- Certified range reduction: q = 2^k * (1+z)/(1-z).
theorem log_bound (q z : ℚ) (k n : ℕ) (two : Box) (out : Box)
    (htwo : two.Holds (Real.log 2)) (hz : 0 ≤ z) (hz' : z < 1)
    (hq : q = 2^k * ((1+z)/(1-z)))
    (hl : out.lo ≤ k*two.lo + series z n)
    (hh : k*two.hi + series z n + tail z n ≤ out.hi) :
    out.Holds (Real.log (q : ℝ)) := by
  have hs := log_series_bound z n hz hz'
  have hr : (0:ℝ) < (((1+z)/(1-z):ℚ):ℝ) := by
    have : 0 < (1+z)/(1-z) := div_pos (by linarith) (by linarith)
    exact_mod_cast this
  have he : Real.log (q:ℝ) = (k:ℝ)*Real.log 2 + Real.log (((1+z)/(1-z):ℚ):ℝ) := by
    rw [hq,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,Real.log_mul (by positivity) (ne_of_gt hr),Real.log_pow]
  rw [Box.Holds,he]
  have hl' : (out.lo:ℝ) ≤ (k:ℝ)*two.lo + (series z n:ℚ) := by exact_mod_cast hl
  have hh' : (k:ℝ)*two.hi + (series z n:ℚ) + (tail z n:ℚ) ≤ (out.hi:ℝ) := by exact_mod_cast hh
  have hm0 := mul_le_mul_of_nonneg_left htwo.1 (Nat.cast_nonneg (α:=ℝ) k)
  have hm1 := mul_le_mul_of_nonneg_left htwo.2 (Nat.cast_nonneg (α:=ℝ) k)
  simp only [Box.Holds,Rat.cast_add] at hs
  constructor <;> linarith
theorem widen_sound {a b : Box} {x : ℝ} (h : a.Holds x)
    (hl : b.lo ≤ a.lo) (hh : a.hi ≤ b.hi) : b.Holds x := by
  have hl' : (b.lo:ℝ) ≤ a.lo := by exact_mod_cast hl
  have hh' : (a.hi:ℝ) ≤ b.hi := by exact_mod_cast hh
  exact ⟨hl'.trans h.1, h.2.trans hh'⟩

def signedTail (z : ℚ) (n : ℕ) : ℚ := 2*(|z|^(2*n+1)/(1-z^2))
theorem log_signed_bound (q z : ℚ) (n : ℕ) (out : Box)
    (hz : |z| < 1) (hq : q = (1+z)/(1-z))
    (hl : out.lo ≤ series z n - signedTail z n)
    (hh : series z n + signedTail z n ≤ out.hi) :
    out.Holds (Real.log (q:ℝ)) := by
  have hz' : |(z:ℝ)| < 1 := by exact_mod_cast hz
  have hs := (abs_le.mp (Real.sum_range_sub_log_div_le hz' n))
  have hl' : (out.lo:ℝ) ≤ (series z n:ℚ) - (signedTail z n:ℚ) := by exact_mod_cast hl
  have hh' : (series z n:ℚ) + (signedTail z n:ℚ) ≤ (out.hi:ℝ) := by exact_mod_cast hh
  simp only [series,signedTail,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_sum,Rat.cast_div,
    Rat.cast_pow,Rat.cast_natCast,Rat.cast_add,Rat.cast_sub,Rat.cast_one,Rat.cast_abs] at hl' hh'
  rw [Box.Holds,hq]
  push_cast
  constructor <;> linarith
end TMM
