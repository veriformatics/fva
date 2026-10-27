import Proofs.LogBounds

namespace Verification

noncomputable def weightedLog (ps : List (ℚ × ℚ)) : ℝ :=
  (ps.map (fun p => (p.1 : ℝ) * Real.log (p.2 : ℝ))).sum

theorem sum_bounds (ps : List (ℚ × ℚ))
    (hp : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 < p.2) :
    ((ps.map (fun p => p.1 * logLo p.2)).sum : ℚ) ≤ weightedLog ps ∧
    weightedLog ps ≤ ((ps.map (fun p => p.1 * logHi p.2)).sum : ℚ) := by
  induction ps with
  | nil => simp [weightedLog]
  | cons p ps ih =>
    have ha := hp p (by simp)
    have hb := ih (fun q hq => hp q (by simp [hq]))
    have hw : (0 : ℝ) ≤ p.1 := by exact_mod_cast ha.1
    have hl := mul_le_mul_of_nonneg_left (certifiedLog p.2 ha.2).1 hw
    have hu := mul_le_mul_of_nonneg_left (certifiedLog p.2 ha.2).2 hw
    simpa only [weightedLog, List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul]
      using And.intro (add_le_add hl hb.1) (add_le_add hu hb.2)

theorem mean_bounds (ps : List (ℚ × ℚ)) (lo hi : ℚ)
    (hp : ∀ p ∈ ps, 0 ≤ p.1 ∧ 0 < p.2)
    (hw : 0 < (ps.map Prod.fst).sum)
    (hl : lo * (ps.map Prod.fst).sum ≤ (ps.map (fun p => p.1 * logLo p.2)).sum)
    (hu : (ps.map (fun p => p.1 * logHi p.2)).sum ≤ hi * (ps.map Prod.fst).sum) :
    (lo : ℝ) ≤ weightedLog ps / ((ps.map Prod.fst).sum : ℚ) ∧
    weightedLog ps / ((ps.map Prod.fst).sum : ℚ) ≤ (hi : ℝ) := by
  have hw' : (0 : ℝ) < ((ps.map Prod.fst).sum : ℚ) := by exact_mod_cast hw
  have hl' : (lo : ℝ) * ((ps.map Prod.fst).sum : ℚ) ≤
      ((ps.map (fun p => p.1 * logLo p.2)).sum : ℚ) := by exact_mod_cast hl
  have hu' : ((ps.map (fun p => p.1 * logHi p.2)).sum : ℚ) ≤
      (hi : ℝ) * ((ps.map Prod.fst).sum : ℚ) := by exact_mod_cast hu
  exact ⟨(le_div_iff₀ hw').mpr (hl'.trans (sum_bounds ps hp).1),
    (div_le_iff₀ hw').mpr ((sum_bounds ps hp).2.trans hu')⟩

end Verification
