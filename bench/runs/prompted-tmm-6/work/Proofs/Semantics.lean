import Proofs.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Verification

theorem positive_pairs : ∀ p ∈ pairs,
    0 < p.1 ∧ 0 < p.2 ∧ p.1 < 1261 ∧ p.2 < 1097 := by
  rw [pairs_eq]
  decide +kernel

theorem log_fraction_lower (n L : ℕ) (hn : 0 < n) (hL : 0 < L) :
    (1 - (L : ℝ)) ≤ Real.log ((n : ℝ) / L) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hn' hL')
  rw [inv_div] at h
  have hd : (L : ℝ) / n ≤ L := (div_le_iff₀ hn').2 (by nlinarith)
  linarith

-- The default edgeR A cutoff excludes no positive pair in this comparison.
theorem cutoff_inactive (p : ℕ × ℕ) (hp : p ∈ pairs) :
    -(10^10 : ℝ) <
      (Real.log ((p.1 : ℝ) / library 0) +
       Real.log ((p.2 : ℝ) / library reference)) / (2 * Real.log 2) := by
  obtain ⟨hp1, hp2, _, _⟩ := positive_pairs p hp
  have h1 := log_fraction_lower p.1 1261 hp1 (by decide)
  have h2 := log_fraction_lower p.2 1097 hp2 (by decide)
  have hlog := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hlog
  rw [reference_eq, lib0, lib3]
  apply (lt_div_iff₀ (by linarith : 0 < 2 * Real.log 2)).2
  norm_num at h1 h2 ⊢
  linarith

end Verification
