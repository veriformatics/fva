import Proofs.Witness
import Proofs.Logs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Proofs

/-- All quartiles are far above edgeR's exceptional-reference threshold 1e-20. -/
theorem quartiles_above_threshold :
    ∀ q ∈ (List.range 7).map (quartile matrix), (1/1000 : ℚ) < q := by
  rw [quartiles_eq]
  decide +kernel

theorem domain_log_bounds (n : Nat) (hn : n ∈ logDomain) :
    0 ≤ Real.log n ∧ Real.log n < 8 := by
  have ha : ∀ m ∈ logDomain, 1 ≤ m := by decide +kernel
  have hb : ∀ m ∈ logDomain, logHi m < 8 := by decide +kernel
  constructor
  · apply Real.log_nonneg
    exact_mod_cast ha n hn
  · exact (log_bounds n hn).2.trans_lt (by exact_mod_cast hb n hn)

/-- Every positive count pair passes the default edgeR A cutoff. Thus omitting
this test in the exact-real model has no effect on this particular input. -/
theorem cutoff_inactive : ∀ j ∈ List.range 7, ∀ p ∈ positivePairs matrix j 3,
    (-10000000000 : ℝ) <
      ((Real.log p.1 - Real.log (library matrix j)) +
        (Real.log p.2 - Real.log (library matrix 3))) / (2 * Real.log 2) := by
  have hd : ∀ j ∈ List.range 7, ∀ p ∈ positivePairs matrix j 3,
      p.1 ∈ logDomain ∧ p.2 ∈ logDomain ∧ library matrix j ∈ logDomain := by
    decide +kernel
  have hr : library matrix 3 ∈ logDomain := by decide +kernel
  intro j hj p hp
  obtain ⟨ho, ht, hn⟩ := hd j hj p hp
  have h1 := domain_log_bounds p.1 ho
  have h2 := domain_log_bounds p.2 ht
  have h3 := domain_log_bounds (library matrix j) hn
  have h4 := domain_log_bounds (library matrix 3) hr
  have htwo := log_two
  norm_num at htwo
  have hden : 0 < 2 * Real.log 2 := by linarith
  apply (lt_div_iff₀ hden).mpr
  nlinarith

end Proofs
