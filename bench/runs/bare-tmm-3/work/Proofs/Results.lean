import Proofs.Model
import Proofs.Certificates

namespace TMMVerification

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Input shape, library sizes and reference are computed from the embedded bytes. -/
theorem input_checked :
    matrix.length = 454 ∧ (∀ r ∈ matrix, r.length = 7) ∧
    rows.length = 454 ∧ edgeFactors.length = 7 ∧ rnaFactors.length = 7 ∧
    indices.map libSize = [1261,621,755,1097,1916,1136,1219] ∧
    indices.map upperQuartile = [4/1261,2/621,2/755,3/1097,5/1916,3/1136,3/1219] ∧
    reference = 3 := by native_decide

/-- Exact ties, including the trimming cutoffs, are checked from the entire matrix. -/
theorem trimming_checked :
    indices.map (fun j => (positivePairs j).length) = [244,195,205,300,259,244,227] ∧
    indices.map (fun j => (keptPairs j).length) = [63,79,76,283,89,95,79] ∧
    (∀ p ∈ centeredTerms 2, p.2 ∈ logArgs) := by native_decide

/-- Rational lower enclosure for a signed logarithm term. -/
def termLower (p : Term) : ℚ :=
  if 0 ≤ p.1 then p.1 * (logCert p.2).lo else p.1 * (logCert p.2).hi

def lowerTerms (ts : List Term) : ℚ := (ts.map termLower).sum

lemma term_lower_sound (p : Term) (h : p.2 ∈ logArgs) :
    (termLower p : ℝ) ≤ (p.1 : ℝ) * Real.log p.2 := by
  obtain ⟨hlo,hhi⟩ := log_bounds_at p.2 h
  unfold termLower
  split_ifs with hc
  · push_cast
    exact mul_le_mul_of_nonneg_left hlo (by exact_mod_cast hc)
  · push_cast
    exact mul_le_mul_of_nonpos_left hhi (by exact_mod_cast (le_of_not_ge hc))

lemma lower_terms_sound (ts : List Term) (h : ∀ p ∈ ts, p.2 ∈ logArgs) :
    (lowerTerms ts : ℝ) ≤ evalTerms ts := by
  induction ts with
  | nil => simp [lowerTerms, evalTerms]
  | cons p ps ih =>
    simp only [lowerTerms, evalTerms, List.map_cons, List.sum_cons, Rat.cast_add]
    exact add_le_add (term_lower_sound p (h p (by simp)))
      (ih (fun q hq => h q (by simp [hq])))

/-- This finite rational computation includes all seven samples' weighted means. -/
theorem centered_log_lower_checked :
    (13/100 : ℚ) < lowerTerms (centeredTerms 2) := by native_decide

/-- A certified real bound, using exp x ≥ 1+x; no floating-point log or exp is trusted. -/
theorem exact_third_factor_gt : (113/100 : ℝ) < exactFactor 2 := by
  have h1 := lower_terms_sound (centeredTerms 2) trimming_checked.2.2
  have h2 : (13/100 : ℝ) < (lowerTerms (centeredTerms 2) : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).2 centered_log_lower_checked
    simpa only [Rat.cast_div, Rat.cast_ofNat] using h
  have h3 := Real.add_one_le_exp (evalTerms (centeredTerms 2))
  unfold exactFactor
  linarith

theorem artifact_values_checked :
    edgeFactors[2]! < (1126/1000 : ℚ) ∧
    rnaFactors[2]! < (1128/1000 : ℚ) ∧
    (9/1000 : ℚ) < |edgeFactors[0]! - rnaFactors[0]!| := by decide +kernel

/-- R1 counterexample at sample 3, with a stronger margin than tolerance 10⁻⁶. -/
theorem R1_counterexample :
    (1/1000 : ℝ) < |(edgeFactors[2]! : ℝ) - exactFactor 2| := by
  have he : (edgeFactors[2]! : ℝ) < 1126/1000 := by
    have h := (Rat.cast_lt (K := ℝ)).2 artifact_values_checked.1
    simpa only [Rat.cast_div, Rat.cast_ofNat] using h
  have hf := exact_third_factor_gt
  rw [abs_of_neg (by linarith)]
  linarith

/-- R2 counterexample, with the documented a_trim parameter taken as 0.05. -/
theorem R2_counterexample :
    (1/1000 : ℝ) < |(rnaFactors[2]! : ℝ) - exactFactor 2| := by
  have he : (rnaFactors[2]! : ℝ) < 1128/1000 := by
    have h := (Rat.cast_lt (K := ℝ)).2 artifact_values_checked.2.1
    simpa only [Rat.cast_div, Rat.cast_ofNat] using h
  have hf := exact_third_factor_gt
  rw [abs_of_neg (by linarith)]
  linarith

/-- R3 fails on the exact decimal values in the first lines of the two files. -/
theorem R3_counterexample :
    (9/1000 : ℝ) < |(edgeFactors[0]! : ℝ) - (rnaFactors[0]! : ℝ)| := by
  have h := (Rat.cast_lt (K := ℝ)).2 artifact_values_checked.2.2
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_abs, Rat.cast_sub] using h

/-- The chosen absolute tolerance for both mathematical TMM requirements is 10⁻⁶. -/
theorem R1_fails : ¬ ∀ j ∈ indices,
    |(edgeFactors[j]! : ℝ) - exactFactor j| ≤ (1/1000000 : ℝ) := by
  intro h
  have hj := h 2 (by simp [indices])
  have hc := R1_counterexample
  linarith

theorem R2_fails : ¬ ∀ j ∈ indices,
    |(rnaFactors[j]! : ℝ) - exactFactor j| ≤ (1/1000000 : ℝ) := by
  intro h
  have hj := h 2 (by simp [indices])
  have hc := R2_counterexample
  linarith

/-- Even the generous absolute-error interpretation of ten decimal places fails. -/
theorem R3_fails : ¬ ∀ j ∈ indices,
    |(edgeFactors[j]! : ℝ) - (rnaFactors[j]! : ℝ)| ≤ (1/10000000000 : ℝ) := by
  intro h
  have hj := h 0 (by simp [indices])
  have hc := R3_counterexample
  linarith

#print axioms R1_fails
#print axioms R2_fails
#print axioms R3_fails
end TMMVerification
