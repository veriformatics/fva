import Proofs.Computation
import Proofs.Artifacts

namespace Verification

lemma default_log_lower : (181 : ℝ)/1000 < rawLog 1 20 2 := by
  have h := weighted_lower 2 defaultPairs default_positive default_weight_positive
  have hr : (181 : ℝ)/1000 <
      (((defaultPairs.map (fun p => weight 2 p * logLower (ratio 2 p))).sum /
        (defaultPairs.map (weight 2)).sum : ℚ) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr default_rational_bound
  have hh := lt_of_lt_of_le hr h
  simpa only [rawLog, show (2 : Nat) ≠ 3 by decide, ↓reduceIte, default_selection] using hh

lemma literal_log_lower : (181 : ℝ)/1000 < rawLog 3 10 2 := by
  have h := weighted_lower 2 literalPairs literal_positive literal_weight_positive
  have hr : (181 : ℝ)/1000 <
      (((literalPairs.map (fun p => weight 2 p * logLower (ratio 2 p))).sum /
        (literalPairs.map (weight 2)).sum : ℚ) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr literal_rational_bound
  have hh := lt_of_lt_of_le hr h
  simpa only [rawLog, show (2 : Nat) ≠ 3 by decide, ↓reduceIte, literal_selection] using hh

lemma factor_pair_relation (a d : Nat)
    (h : (181 : ℝ)/1000 < rawLog a d 2) :
    (1181 : ℝ)/1000 * factor a d 3 < factor a d 2 := by
  have hs : rawLog a d 3 = 0 := by simp [rawLog]
  have hr : (1181 : ℝ)/1000 < Real.exp (rawLog a d 2) := by
    have he := Real.add_one_le_exp (rawLog a d 2)
    linarith
  have hid : factor a d 2 = Real.exp (rawLog a d 2) * factor a d 3 := by
    simp only [factor, hs, zero_sub, Real.exp_sub, Real.exp_neg]
    ring
  rw [hid]
  exact mul_lt_mul_of_pos_right hr (Real.exp_pos _)

lemma pair_obstruction (x y s t : ℝ)
    (hspec : (1181 : ℝ)/1000 * y < x)
    (hfile : s + tolerance < (1181 : ℝ)/1000 * (t - tolerance)) :
    ¬ (|x-s| ≤ tolerance ∧ |y-t| ≤ tolerance) := by
  rintro ⟨hx,hy⟩
  have hx' := (abs_le.mp hx).2
  have hy' := (abs_le.mp hy).1
  linarith

theorem R1_pair_fails :
    ¬ (|factor 1 20 2 - (edge[2]! : ℝ)| ≤ tolerance ∧
       |factor 1 20 3 - (edge[3]! : ℝ)| ≤ tolerance) := by
  apply pair_obstruction _ _ _ _ (factor_pair_relation 1 20 default_log_lower)
  simpa only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one, Nat.cast_ofNat, tolerance] using
    (Rat.cast_lt (K := ℝ)).mpr edge_pair_gap

theorem R1_fails : ¬ (∀ j ∈ List.range 7,
    |factor 1 20 j - (edge[j]! : ℝ)| ≤ tolerance) := by
  intro h
  exact R1_pair_fails ⟨h 2 (by decide),h 3 (by decide)⟩

theorem R2_pair_fails :
    ¬ (|factor 1 20 2 - (rna[2]! : ℝ)| ≤ tolerance ∧
       |factor 1 20 3 - (rna[3]! : ℝ)| ≤ tolerance) := by
  apply pair_obstruction _ _ _ _ (factor_pair_relation 1 20 default_log_lower)
  simpa only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one, Nat.cast_ofNat, tolerance] using
    (Rat.cast_lt (K := ℝ)).mpr rna_pair_gap

theorem R2_fails : ¬ (∀ j ∈ List.range 7,
    |factor 1 20 j - (rna[j]! : ℝ)| ≤ tolerance) := by
  intro h
  exact R2_pair_fails ⟨h 2 (by decide),h 3 (by decide)⟩

-- The RNAnorm prose bullet says to trim A with m_trim; even that literal reading fails.
theorem R2_literal_fails : ¬ (∀ j ∈ List.range 7,
    |factor 3 10 j - (rna[j]! : ℝ)| ≤ tolerance) := by
  intro h
  have hf : ¬ (|factor 3 10 2 - (rna[2]! : ℝ)| ≤ tolerance ∧
      |factor 3 10 3 - (rna[3]! : ℝ)| ≤ tolerance) := by
    apply pair_obstruction _ _ _ _ (factor_pair_relation 3 10 literal_log_lower)
    simpa only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one, Nat.cast_ofNat, tolerance] using
    (Rat.cast_lt (K := ℝ)).mpr rna_pair_gap
  exact hf ⟨h 2 (by decide),h 3 (by decide)⟩

theorem R3_fails : ¬ (∀ j ∈ List.range 7,
    |(edge[j]! : ℝ) - (rna[j]! : ℝ)| ≤ tolerance) := by
  intro h
  have hg : (1 : ℝ)/1000 < |(edge[0]! : ℝ) - (rna[0]! : ℝ)| := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Nat.cast_ofNat, Rat.cast_abs, Rat.cast_sub] using
      (Rat.cast_lt (K := ℝ)).mpr (R3_all_seven_gaps 0 (by decide))
  have hh := h 0 (by decide)
  have ht : tolerance < (1 : ℝ)/1000 := by norm_num [tolerance]
  exact (not_lt_of_ge hh) (lt_trans ht hg)


end Verification
