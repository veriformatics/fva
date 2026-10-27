import Proofs.Certificates

namespace Verification
set_option maxRecDepth 100000
set_option maxHeartbeats 0
deriving instance Inhabited for LogCertificate

lemma cast_lt {a b : ℚ} (h : a < b) : (a:ℝ) < (b:ℝ) := by exact_mod_cast h

-- Finite computation checks the complete matrix and average ranks, not a sample.
theorem data_shape : counts.length = 454 ∧ (∀ r ∈ counts, r.length = 7) ∧
    (List.range 7).map library = [1261,621,755,1097,1916,1136,1219] := by native_decide

theorem reference_choice : referenceIsFourth := by native_decide

-- All finite positive pairs clear the documented A cutoff: product > 2^-24
-- implies A > -12, which is much greater than -1e10.
-- Every non-reference comparison has an M value > 1, so its near-zero shortcut is inactive.
theorem dataset_conditions : nonzeroRows.length = 454 ∧ ∀ j : Fin 7,
    ((eligible j.val).all fun r => decide (0 < variance j.val r ∧
      (1:ℚ)/2^24 < (r[j.val]!:ℚ)*r[3]!/((library j.val:ℚ)*library 3))) = true ∧
    (j.val ≠ 3 → ((eligible j.val).any fun r => decide
      ((2:ℚ) < (r[j.val]!:ℚ)*library 3/((r[3]!:ℚ)*library j.val))) = true) := by
  native_decide

theorem exact_tie_witness : (counts[162]!)[0]! = 8 ∧ (counts[162]!)[3]! = 13 ∧
    (counts[354]!)[0]! = 13 ∧ (counts[354]!)[3]! = 8 ∧
    (eligible 0).length = 244 ∧
    rankTwice ((eligible 0).map (aKey 0)) 104 = 465 := by native_decide

theorem forms_match : ∀ j : Fin 7,
    (forms[j.val]!.map fun (w,c) => (w,c.q)) = terms j.val := by native_decide

theorem certificates_valid : ∀ j : Fin 7, (forms[j.val]!.all fun t => decide t.2.valid) = true := by
  native_decide

theorem endpoints_valid : ∀ j : Fin 7,
    lowerCerts[j.val]!.valid ∧ upperCerts[j.val]!.valid ∧
    lowerCerts[j.val]!.q = lows[j.val]! ∧ upperCerts[j.val]!.q = highs[j.val]! ∧
    0 < lows[j.val]! ∧ 0 < highs[j.val]! := by native_decide

def meanCenter : ℚ := (∑ j ∈ Finset.range 7, center forms[j]!) / 7
def meanError : ℚ := (∑ j ∈ Finset.range 7, error forms[j]!) / 7

theorem numeric_enclosures : ∀ j : Fin 7,
    lowerCerts[j.val]!.rounded + 1/1000000 <
      center forms[j.val]! - error forms[j.val]! - (meanCenter + meanError) ∧
    center forms[j.val]! + error forms[j.val]! - (meanCenter - meanError) <
      upperCerts[j.val]!.rounded - 1/1000000 := by native_decide

lemma raw_bound (j : Fin 7) :
    |rawLog j.val - (center forms[j.val]! : ℝ)| ≤ (error forms[j.val]! : ℝ) := by
  have hm : rawLog j.val = value forms[j.val]! := by
    rw [rawLog, ← forms_match j]
    simp [value, List.map_map, Function.comp_def]
  rw [hm]
  apply form_sound
  intro t ht
  exact of_decide_eq_true ((List.all_eq_true.mp (certificates_valid j)) t ht)

lemma mean_bound :
    (meanCenter:ℝ) - meanError ≤ meanLog ∧ meanLog ≤ (meanCenter:ℝ) + meanError := by
  have hlo : ∀ j ∈ Finset.range 7,
      ((center forms[j]! - error forms[j]! : ℚ):ℝ) ≤ rawLog j := by
    intro j hj
    have h := (abs_sub_le_iff.mp (raw_bound ⟨j, Finset.mem_range.mp hj⟩)).2
    push_cast
    linarith
  have hhi : ∀ j ∈ Finset.range 7,
      rawLog j ≤ ((center forms[j]! + error forms[j]! : ℚ):ℝ) := by
    intro j hj
    have h := (abs_sub_le_iff.mp (raw_bound ⟨j, Finset.mem_range.mp hj⟩)).1
    push_cast
    linarith
  have hl := Finset.sum_le_sum hlo
  have hh := Finset.sum_le_sum hhi
  simp only [Rat.cast_sub, Rat.cast_add, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hl hh
  unfold meanCenter meanError meanLog
  push_cast
  constructor <;> linarith

-- Tight enclosures of the exact-real TMM model, for every sample.
theorem factor_enclosures (j : Fin 7) :
    (lows[j.val]! : ℝ) < factor j.val ∧ factor j.val < (highs[j.val]! : ℝ) := by
  obtain ⟨hlv, huv, hlq, huq, hlp, hup⟩ := endpoints_valid j
  have hloglo := lowerCerts[j.val]!.sound hlv
  have hloghi := upperCerts[j.val]!.sound huv
  rw [hlq] at hloglo
  rw [huq] at hloghi
  have hn := numeric_enclosures j
  have hn1 := cast_lt hn.1
  have hn2 := cast_lt hn.2
  push_cast at hn1 hn2
  obtain ⟨hr1,hr2⟩ := abs_sub_le_iff.mp (raw_bound j)
  obtain ⟨hm1,hm2⟩ := mean_bound
  obtain ⟨hll,hlr⟩ := abs_sub_le_iff.mp hloglo
  obtain ⟨hul,hur⟩ := abs_sub_le_iff.mp hloghi
  have hl : Real.log (lows[j.val]!:ℝ) < rawLog j.val - meanLog := by linarith
  have hu : rawLog j.val - meanLog < Real.log (highs[j.val]!:ℝ) := by linarith
  constructor
  · have h := Real.exp_lt_exp.mpr hl
    rw [Real.exp_log (by exact_mod_cast hlp)] at h
    exact h
  · have h := Real.exp_lt_exp.mpr hu
    rw [Real.exp_log (by exact_mod_cast hup)] at h
    exact h

-- These deliberately explicit tolerances quantify the accuracy actually proved.
theorem artifact_numeric_bounds : ∀ j : Fin 7,
    edgeFactors[j.val]! - highs[j.val]! > -23/1000 ∧
    edgeFactors[j.val]! - lows[j.val]! < 23/1000 ∧
    rnaFactors[j.val]! - highs[j.val]! > -21/1000 ∧
    rnaFactors[j.val]! - lows[j.val]! < 21/1000 := by native_decide

theorem R1_at_0023 (j : Fin 7) :
    |(edgeFactors[j.val]!:ℝ) - factor j.val| < 23/1000 := by
  obtain ⟨hl,hu⟩ := factor_enclosures j
  obtain ⟨h1,h2,_,_⟩ := artifact_numeric_bounds j
  have h1' := cast_lt h1
  have h2' := cast_lt h2
  push_cast at h1' h2'
  rw [abs_lt]
  constructor <;> linarith

theorem R2_at_0021 (j : Fin 7) :
    |(rnaFactors[j.val]!:ℝ) - factor j.val| < 21/1000 := by
  obtain ⟨hl,hu⟩ := factor_enclosures j
  obtain ⟨_,_,h1,h2⟩ := artifact_numeric_bounds j
  have h1' := cast_lt h1
  have h2' := cast_lt h2
  push_cast at h1' h2'
  rw [abs_lt]
  constructor <;> linarith

-- Exact counterexample to R3 on the shipped decimal strings (sample 1).
theorem R3_counterexample :
    edgeFactors[0]! - rnaFactors[0]! = (931142302732627:ℚ)/100000000000000000 ∧
    |edgeFactors[0]! - rnaFactors[0]!| > (1:ℚ)/10^10 := by native_decide

-- The files also fail a fine tolerance against this exact-real model.
theorem first_values_lower : (99099:ℚ)/100000 < edgeFactors[0]! ∧
    (98168:ℚ)/100000 < rnaFactors[0]! := by native_decide

theorem fine_tolerance_failure :
    |(edgeFactors[0]!:ℝ) - factor 0| > (1:ℝ)/10^10 ∧
    |(rnaFactors[0]!:ℝ) - factor 0| > (1:ℝ)/10^10 := by
  have hf := (factor_enclosures ⟨0,by omega⟩).2
  norm_num [highs] at hf
  have he := cast_lt first_values_lower.1
  have hr := cast_lt first_values_lower.2
  push_cast at he hr
  constructor
  · have hh := le_abs_self ((edgeFactors[0]!:ℝ) - factor 0)
    linarith
  · have hh := le_abs_self ((rnaFactors[0]!:ℝ) - factor 0)
    linarith

-- A small kernel-checked witness, independent of native computation and of TMM.
-- Artifacts.lean pins the exact text containing these two decimal numerals.
theorem R3_decimal_witness :
    (99099942459293067/100000000000000000:ℚ) -
      9816880015656044/10000000000000000 = 931142302732627/100000000000000000 ∧
    (99099942459293067/100000000000000000:ℚ) -
      9816880015656044/10000000000000000 > 1/10^10 := by norm_num

#print axioms R1_at_0023
#print axioms R2_at_0021
#print axioms fine_tolerance_failure
#print axioms R3_counterexample
#print axioms R3_decimal_witness
end Verification
