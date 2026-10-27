import Proofs.Model
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace Proofs.Bounds

structure I where
  lo : ℚ
  hi : ℚ

def I.Holds (b : I) (x : ℝ) : Prop := (b.lo : ℝ) ≤ x ∧ x ≤ (b.hi : ℝ)

def I.add (a b : I) : I := ⟨a.lo + b.lo, a.hi + b.hi⟩
def I.sub (a b : I) : I := ⟨a.lo - b.hi, a.hi - b.lo⟩
def I.scale (q : ℚ) (a : I) : I := ⟨q * a.lo, q * a.hi⟩
def I.div (a : I) (q : ℚ) : I := ⟨a.lo / q, a.hi / q⟩
def I.zero : I := ⟨0, 0⟩

theorem holds_add {a b : I} {x y : ℝ} (ha : a.Holds x) (hb : b.Holds y) :
    (a.add b).Holds (x + y) := by
  dsimp [I.Holds, I.add] at *
  push_cast
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

theorem holds_sub {a b : I} {x y : ℝ} (ha : a.Holds x) (hb : b.Holds y) :
    (a.sub b).Holds (x - y) := by
  dsimp [I.Holds, I.sub] at *
  push_cast
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

theorem holds_scale {a : I} {x : ℝ} {q : ℚ} (hq : 0 ≤ q) (ha : a.Holds x) :
    (a.scale q).Holds ((q : ℝ) * x) := by
  dsimp [I.Holds, I.scale] at *
  push_cast
  have h : (0 : ℝ) ≤ q := by exact_mod_cast hq
  exact ⟨mul_le_mul_of_nonneg_left ha.1 h, mul_le_mul_of_nonneg_left ha.2 h⟩

theorem holds_div {a : I} {x : ℝ} {q : ℚ} (hq : 0 ≤ q) (ha : a.Holds x) :
    (a.div q).Holds (x / (q : ℝ)) := by
  dsimp [I.Holds, I.div] at *
  push_cast
  have h : (0 : ℝ) ≤ q := by exact_mod_cast hq
  exact ⟨div_le_div_of_nonneg_right ha.1 h, div_le_div_of_nonneg_right ha.2 h⟩

def isum (xs : List I) : I := xs.foldr I.add I.zero

theorem holds_sum {α : Type} (xs : List α) (b : α → I) (f : α → ℝ)
    (h : ∀ x ∈ xs, (b x).Holds (f x)) :
    (isum (xs.map b)).Holds ((xs.map f).sum) := by
  induction xs with
  | nil => norm_num [isum, I.Holds, I.zero]
  | cons x xs ih =>
    exact holds_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

def series (z : ℚ) : ℚ :=
  2 * ((Finset.range 16).sum (fun i => z ^ (2 * i + 1) / (2 * i + 1)))

def tail (z : ℚ) : ℚ := 2 * z ^ 33 / (1 - z ^ 2)

theorem log_small (q : ℚ) (hq : 1 ≤ q) :
    (⟨series ((q - 1) / (q + 1)),
      series ((q - 1) / (q + 1)) + tail ((q - 1) / (q + 1))⟩ : I).Holds
      (Real.log (q : ℝ)) := by
  let z : ℝ := ((q : ℝ) - 1) / ((q : ℝ) + 1)
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hden : 0 < (q : ℝ) + 1 := by linarith
  have hz0 : 0 ≤ z := div_nonneg (by linarith) hden.le
  have hz1 : z < 1 := (div_lt_one hden).2 (by linarith)
  have heq : (1 + z) / (1 - z) = (q : ℝ) := by
    dsimp [z]
    field_simp
    <;> ring
  have hlo := Real.sum_range_le_log_div hz0 hz1 16
  have hhi := Real.log_div_le_sum_range_add hz0 hz1 16
  rw [heq] at hlo hhi
  dsimp [I.Holds, series, tail]
  push_cast
  change 2 * (∑ i ∈ Finset.range 16, z ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) ≤ _ ∧
    _ ≤ 2 * (∑ i ∈ Finset.range 16, z ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) +
      2 * z ^ 33 / (1 - z ^ 2)
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hlo hhi
  rw [mul_div_assoc]
  constructor <;> linarith

def logLow (n k : Nat) : ℚ :=
  let q : ℚ := n / 2 ^ k
  series ((q - 1) / (q + 1)) + k * series (1 / 3)

def logHigh (n k : Nat) : ℚ :=
  let q : ℚ := n / 2 ^ k
  logLow n k + tail ((q - 1) / (q + 1)) + k * tail (1 / 3)

/-- Rational checks certify a natural logarithm; no floating arithmetic is trusted. -/
theorem log_nat (n k : Nat) (lo hi : ℚ)
    (hq : (1 : ℚ) ≤ n / 2 ^ k)
    (hlo : lo ≤ logLow n k) (hhi : logHigh n k ≤ hi) :
    (⟨lo, hi⟩ : I).Holds (Real.log n) := by
  let q : ℚ := n / 2 ^ k
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hn : (n : ℝ) = (q : ℝ) * 2 ^ k := by
    dsimp [q]
    push_cast
    field_simp
  have heq : Real.log (n : ℝ) = Real.log (q : ℝ) + k * Real.log 2 := by
    rw [hn, Real.log_mul (ne_of_gt hqR) (ne_of_gt hpow), Real.log_pow]
  have h1 := log_small q hq
  have h2 := log_small 2 (by norm_num)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  dsimp [I.Holds] at h1 h2 ⊢
  norm_num only [show ((2 : ℚ) - 1) / (2 + 1) = 1 / 3 by norm_num] at h2
  have hl : (lo : ℝ) ≤ logLow n k := by exact_mod_cast hlo
  have hh : (logHigh n k : ℝ) ≤ hi := by exact_mod_cast hhi
  dsimp [logLow, logHigh] at hl hh
  push_cast at hl hh
  push_cast only [Rat.cast_add] at h1 h2
  rw [heq]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2,
    mul_le_mul_of_nonneg_left h2.1 hk, mul_le_mul_of_nonneg_left h2.2 hk]

theorem holds_weaken {a b : I} {x : ℝ} (ha : a.Holds x)
    (hl : b.lo ≤ a.lo) (hh : a.hi ≤ b.hi) : b.Holds x := by
  have hl' : (b.lo : ℝ) ≤ a.lo := by exact_mod_cast hl
  have hh' : (a.hi : ℝ) ≤ b.hi := by exact_mod_cast hh
  exact ⟨hl'.trans ha.1, ha.2.trans hh'⟩

open Model

def ratioI (logs : Nat → I) (l r : Nat) (p : Nat × Nat) : I :=
  (((logs p.1).sub (logs p.2)).add (logs r)).sub (logs l)

def rawI (logs : Nat → I) (l r : Nat) (ps : List (Nat × Nat)) : I :=
  (isum (ps.map (fun p => (ratioI logs l r p).scale (weight l r p)))).div
    ((ps.map (weight l r)).sum)

theorem raw_sound (logs : Nat → I) (l r : Nat) (ps : List (Nat × Nat))
    (hl : (logs l).Holds (Real.log l)) (hr : (logs r).Holds (Real.log r))
    (hp : ∀ p ∈ ps, (logs p.1).Holds (Real.log p.1) ∧
      (logs p.2).Holds (Real.log p.2))
    (hw : ∀ p ∈ ps, 0 ≤ weight l r p) :
    (rawI logs l r ps).Holds
      ((ps.map (fun p => (weight l r p : ℝ) * logRatio l r p)).sum /
        ((ps.map (weight l r)).sum : ℝ)) := by
  apply holds_div
  · apply List.sum_nonneg
    intro w hwmem
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hwmem
    exact hw p hp
  · apply holds_sum
    intro p hpm
    apply holds_scale (hw p hpm)
    exact holds_sub (holds_add (holds_sub (hp p hpm).1 (hp p hpm).2) hr) hl

theorem log_quotient (a b : Nat) (ha : 0 < a) (hb : 0 < b)
    {ia ib : I} (hia : ia.Holds (Real.log a)) (hib : ib.Holds (Real.log b)) :
    (ia.sub ib).Holds (Real.log ((a : ℚ) / b : ℚ)) := by
  push_cast
  rw [Real.log_div (by positivity : (a : ℝ) ≠ 0) (by positivity : (b : ℝ) ≠ 0)]
  exact holds_sub hia hib

theorem exp_enclose {z : ℝ} {iz il ih : I} {lo hi : ℚ}
    (hz : iz.Holds z)
    (hl : il.Holds (Real.log (lo : ℝ))) (hh : ih.Holds (Real.log (hi : ℝ)))
    (hlo : 0 < lo) (hhi : 0 < hi)
    (hleft : il.hi ≤ iz.lo) (hright : iz.hi ≤ ih.lo) :
    (lo : ℝ) ≤ Real.exp z ∧ Real.exp z ≤ (hi : ℝ) := by
  have hleft' : (il.hi : ℝ) ≤ iz.lo := by exact_mod_cast hleft
  have hright' : (iz.hi : ℝ) ≤ ih.lo := by exact_mod_cast hright
  have hlo' : (0 : ℝ) < lo := by exact_mod_cast hlo
  have hhi' : (0 : ℝ) < hi := by exact_mod_cast hhi
  constructor
  · calc
      (lo : ℝ) = Real.exp (Real.log (lo : ℝ)) := (Real.exp_log hlo').symm
      _ ≤ Real.exp z := Real.exp_le_exp.mpr (hl.2.trans (hleft'.trans hz.1))
  · calc
      Real.exp z ≤ Real.exp (Real.log (hi : ℝ)) :=
        Real.exp_le_exp.mpr (hz.2.trans (hright'.trans hh.1))
      _ = (hi : ℝ) := Real.exp_log hhi'

theorem abs_error {lo hi y tolerance : ℚ} {x : ℝ}
    (hx : (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ))
    (hl : y - tolerance ≤ lo) (hh : hi ≤ y + tolerance) :
    |(y : ℝ) - x| ≤ (tolerance : ℝ) := by
  have hl' : (y : ℝ) - tolerance ≤ lo := by exact_mod_cast hl
  have hh' : (hi : ℝ) ≤ (y : ℝ) + tolerance := by exact_mod_cast hh
  exact abs_le.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩

end Proofs.Bounds
