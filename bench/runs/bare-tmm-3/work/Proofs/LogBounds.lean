import Mathlib

namespace TMMVerification
open Finset

/-- Eight terms of the atanh series, with a rigorous remainder. -/
def series (t : ℚ) : ℚ := ∑ i ∈ range 8, t ^ (2 * i + 1) / (2 * i + 1)
def remainder (t : ℚ) : ℚ := t ^ 17 / (1 - t ^ 2)

lemma series_bounds (t : ℚ) (h0 : 0 ≤ t) (h1 : t < 1) :
    ((2 * series t : ℚ) : ℝ) ≤ Real.log (((1+t)/(1-t) : ℚ) : ℝ) ∧
    Real.log (((1+t)/(1-t) : ℚ) : ℝ) ≤ ((2 * (series t + remainder t) : ℚ) : ℝ) := by
  have h0' : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast h0
  have h1' : (t : ℝ) < 1 := by exact_mod_cast h1
  have lo := Real.sum_range_le_log_div h0' h1' 8
  have hi := Real.log_div_le_sum_range_add h0' h1' 8
  have hs : (series t : ℝ) = ∑ i ∈ range 8, (t : ℝ) ^ (2*i+1) / (2*i+1) := by
    simp [series]
  have he : (remainder t : ℝ) = (t : ℝ)^17 / (1 - (t : ℝ)^2) := by
    simp [remainder]
  constructor <;> push_cast
  · rw [hs]
    linarith
  · rw [hs, he]
    linarith

structure LogCert where
  arg : Nat
  k : Nat
  t : ℚ
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

def LogCert.valid (c : LogCert) : Prop :=
  0 ≤ c.t ∧ c.t < 1 ∧
  (c.arg : ℚ) = 2^c.k * ((1+c.t)/(1-c.t)) ∧
  c.lo ≤ (c.k : ℚ) * (2 * series (1/3)) + 2 * series c.t ∧
  (c.k : ℚ) * (2 * (series (1/3) + remainder (1/3))) +
    2 * (series c.t + remainder c.t) ≤ c.hi
  deriving Decidable

lemma LogCert.sound (c : LogCert) (h : c.valid) :
    (c.lo : ℝ) ≤ Real.log c.arg ∧ Real.log c.arg ≤ (c.hi : ℝ) := by
  obtain ⟨h0,h1,heq,hlo,hhi⟩ := h
  have ht := series_bounds c.t h0 h1
  have htwo := series_bounds (1/3) (by norm_num) (by norm_num)
  norm_num at htwo
  have hp : (0 : ℝ) < (1 + (c.t : ℝ)) / (1 - (c.t : ℝ)) := by
    have h0' : (0 : ℝ) ≤ (c.t : ℝ) := by exact_mod_cast h0
    have h1' : (c.t : ℝ) < 1 := by exact_mod_cast h1
    positivity
  have heq' : (c.arg : ℝ) = (2:ℝ)^c.k * ((1+(c.t:ℝ))/(1-(c.t:ℝ))) := by
    exact_mod_cast heq
  rw [heq', Real.log_mul (by positivity) (ne_of_gt hp), Real.log_pow]
  push_cast at ht
  have hlo' : (c.lo : ℝ) ≤ (c.k : ℝ) * (2 * (series (1/3) : ℝ)) +
      2 * (series c.t : ℝ) := by exact_mod_cast hlo
  have hhi' : (c.k : ℝ) * (2 * ((series (1/3) : ℝ) + (remainder (1/3) : ℝ))) +
      2 * ((series c.t : ℝ) + (remainder c.t : ℝ)) ≤ (c.hi : ℝ) := by exact_mod_cast hhi
  have hmullo := mul_le_mul_of_nonneg_left htwo.1 (Nat.cast_nonneg c.k : (0:ℝ) ≤ c.k)
  have hmulhi := mul_le_mul_of_nonneg_left htwo.2 (Nat.cast_nonneg c.k : (0:ℝ) ≤ c.k)
  constructor <;> linarith [ht.1, ht.2]

end TMMVerification
