import Proofs.Certificates
import Proofs.Counterexample
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace TMM

-- These two theorems use the concrete trimming masks observed in source replay.
-- They do not assert equivalence of an R/Python floating-point runtime to Lean.
theorem r1_source_mask_model : ∀ i ∈ List.range 7,
    |(edgeFactors[i]! : ℝ) - factor edgeMasks i| ≤ ((1:ℚ)/10^12 : ℝ) := by
  intro i hi
  have h := edge_enclosed i hi
  have e : edgeEndpoints i =
      ⟨edgeFactors[i]!-1/10^12, edgeFactors[i]!+1/10^12⟩ := by
    have hi' : i < 7 := List.mem_range.mp hi
    interval_cases i <;> decide +kernel
  rw [e] at h
  simp only [Box.Holds,Rat.cast_sub,Rat.cast_add] at h
  exact abs_le.mpr ⟨by linarith [h.2], by linarith [h.1]⟩

theorem r2_source_mask_model : ∀ i ∈ List.range 7,
    |(rnaFactors[i]! : ℝ) - factor rnaMasks i| ≤ ((1:ℚ)/10^12 : ℝ) := by
  intro i hi
  have h := rna_enclosed i hi
  have e : rnaEndpoints i =
      ⟨rnaFactors[i]!-1/10^12, rnaFactors[i]!+1/10^12⟩ := by
    have hi' : i < 7 := List.mem_range.mp hi
    interval_cases i <;> decide +kernel
  rw [e] at h
  simp only [Box.Holds,Rat.cast_sub,Rat.cast_add] at h
  exact abs_le.mpr ⟨by linarith [h.2], by linarith [h.1]⟩

-- Both files differ materially from the exact-rank, exact-real interpretation.
theorem r1_exact_rank_counterexample :
    ((1:ℚ)/1000 : ℝ) < |(edgeFactors[0]! : ℝ) - factor idealMasks 0| := by
  have h := ideal_0_enclosed
  have he : ((975528:ℚ)/10^6 : ℝ) < (edgeFactors[0]! : ℝ) - ((1:ℚ)/1000 :ℝ) := by
    norm_num [edgeFactors]
  have hu : factor idealMasks 0 ≤ ((975528:ℚ)/10^6 :ℝ) := by
    convert h.2 using 1; norm_num [idealEndpoints]
  exact lt_of_lt_of_le (by linarith) (le_abs_self _)

theorem r2_exact_rank_counterexample :
    ((1:ℚ)/1000 : ℝ) < |(rnaFactors[0]! : ℝ) - factor idealMasks 0| := by
  have h := ideal_0_enclosed
  have he : ((975528:ℚ)/10^6 : ℝ) < (rnaFactors[0]! : ℝ) - ((1:ℚ)/1000 :ℝ) := by
    norm_num [rnaFactors]
  have hu : factor idealMasks 0 ≤ ((975528:ℚ)/10^6 :ℝ) := by
    convert h.2 using 1; norm_num [idealEndpoints]
  exact lt_of_lt_of_le (by linarith) (le_abs_self _)

theorem quartile_fallback_inactive : ∀ i ∈ List.range 7, (1:ℚ)/10^20 < quartile i := by
  native_decide

-- Formal support for the omitted finite-value/A-cutoff filters in the exact model.
def supported (i : ℕ) (p : Pair) : Prop :=
  p.1 ∈ logKeys ∧ p.2 ∈ logKeys ∧ libs[i]! ∈ logKeys ∧ libs[3]! ∈ logKeys ∧
  -16 < (logBox p.1).lo+(logBox p.2).lo-(logBox (libs[i]!)).hi-(logBox (libs[3]!)).hi
instance (i : ℕ) (p : Pair) : Decidable (supported i p) := by
  unfold supported
  infer_instance

theorem all_eligible_supported : ∀ i ∈ List.range 7, ∀ p ∈ eligible i, supported i p := by
  native_decide

noncomputable def aValue (i : ℕ) (p : Pair) : ℝ :=
  (Real.log p.1 + Real.log p.2 - Real.log (libs[i]!) - Real.log (libs[3]!)) /
  (2*Real.log 2)

theorem cutoff_inactive : ∀ i ∈ List.range 7, ∀ p ∈ eligible i,
    (-10000000000:ℝ) < aValue i p := by
  intro i hi p hp
  have h := all_eligible_supported i hi p hp
  have h1 := (logBox_sound h.1).1
  have h2 := (logBox_sound h.2.1).1
  have h3 := (logBox_sound h.2.2.1).2
  have h4 := (logBox_sound h.2.2.2.1).2
  have h5 : (-16:ℝ) < (logBox p.1).lo+(logBox p.2).lo-
      (logBox (libs[i]!)).hi-(logBox (libs[3]!)).hi := by
    exact_mod_cast h.2.2.2.2
  have h6 := logTwo_sound.1
  have h7 : (1/2:ℝ) < Real.log 2 := by
    norm_num [logTwoBox] at h6
    linarith
  have hn : (-16:ℝ) < Real.log p.1 + Real.log p.2 - Real.log (libs[i]!) - Real.log (libs[3]!) := by linarith
  have hd : (0:ℝ) < 2*Real.log 2 := by linarith
  unfold aValue
  apply (lt_div_iff₀ hd).mpr
  nlinarith

-- Native finite checks and their trust requirements are exposed by Proofs/Audit.lean.
end TMM
