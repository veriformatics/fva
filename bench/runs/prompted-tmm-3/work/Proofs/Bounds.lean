import Proofs.Certificate
namespace Verification
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- A tiny exact certificate for an upper bound on a logarithm.
theorem log_upper (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y^8) :
    Real.log x ≤ 8 * (y - 1) := by
  calc
    Real.log x ≤ Real.log (y^8) := Real.log_le_log hx hxy
    _ = 8 * Real.log y := Real.log_pow y 8
    _ ≤ 8 * (y - 1) := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hy) (by norm_num)

theorem selected_eq : kept 0 1 20 = selected := by
  unfold kept pairs ratio
  rw [reference_is_four]
  simp only [lib_zero, lib_three]
  decide +kernel

theorem literal_selected_eq : kept 0 3 10 = literalSelected := by
  unfold kept pairs ratio
  rw [reference_is_four]
  simp only [lib_zero, lib_three]
  decide +kernel

def upper (ps : List (Nat × Nat)) : ℚ :=
  (ps.map fun p => weight 0 p * (8 * (root p - 1))).sum

def mass (ps : List (Nat × Nat)) : ℚ := (ps.map (weight 0)).sum

theorem selected_valid : ∀ p ∈ selected ++ literalSelected,
    0 < ratio 0 p ∧ 0 < root p ∧ ratio 0 p ≤ (root p)^8 ∧ 0 ≤ weight 0 p := by
  unfold ratio weight
  rw [reference_is_four]
  simp only [lib_zero, lib_three]
  decide +kernel

theorem selected_numeric : 0 < mass selected ∧ upper selected ≤ (3/125 : ℚ) * mass selected := by
  unfold mass upper weight
  rw [reference_is_four]
  simp only [lib_zero, lib_three]
  decide +kernel

theorem literal_numeric : 0 < mass literalSelected ∧
    upper literalSelected ≤ (3/125 : ℚ) * mass literalSelected := by
  unfold mass upper weight
  rw [reference_is_four]
  simp only [lib_zero, lib_three]
  decide +kernel

theorem weighted_bound (ps : List (Nat × Nat))
    (hv : ∀ p ∈ ps, 0 < ratio 0 p ∧ 0 < root p ∧ ratio 0 p ≤ (root p)^8 ∧ 0 ≤ weight 0 p)
    (hn : 0 < mass ps ∧ upper ps ≤ (3/125 : ℚ) * mass ps) :
    (ps.map fun p => (weight 0 p : ℝ) * Real.log (ratio 0 p : ℝ)).sum /
      (mass ps : ℝ) ≤ 3/125 := by
  have ht := List.sum_le_sum (l := ps) (fun p hp =>
    mul_le_mul_of_nonneg_left
      (log_upper (ratio 0 p) (root p) (by exact_mod_cast (hv p hp).1)
        (by exact_mod_cast (hv p hp).2.1) (by exact_mod_cast (hv p hp).2.2.1))
      (by exact_mod_cast (hv p hp).2.2.2))
  have hu : (ps.map fun p => (weight 0 p : ℝ) * (8 * ((root p : ℝ) - 1))).sum =
      (upper ps : ℝ) := by
    simp [upper, Rat.cast_list_sum, List.map_map]
  rw [hu] at ht
  have hm : (0 : ℝ) < mass ps := by exact_mod_cast hn.1
  apply (div_le_iff₀ hm).2
  exact ht.trans (by exact_mod_cast hn.2)

theorem raw_bound : raw 0 1 20 ≤ 3/125 := by
  have hv : ∀ p ∈ selected, 0 < ratio 0 p ∧ 0 < root p ∧ ratio 0 p ≤ (root p)^8 ∧ 0 ≤ weight 0 p :=
    fun p hp => selected_valid p (List.mem_append_left _ hp)
  simpa [raw, reference_is_four, selected_eq, mass] using weighted_bound selected hv selected_numeric

theorem literal_raw_bound : raw 0 3 10 ≤ 3/125 := by
  have hv : ∀ p ∈ literalSelected, 0 < ratio 0 p ∧ 0 < root p ∧ ratio 0 p ≤ (root p)^8 ∧ 0 ≤ weight 0 p :=
    fun p hp => selected_valid p (List.mem_append_right _ hp)
  simpa [raw, reference_is_four, literal_selected_eq, mass] using
    weighted_bound literalSelected hv literal_numeric
end Verification
