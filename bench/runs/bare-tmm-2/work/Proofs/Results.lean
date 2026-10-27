import Proofs.Model

namespace TMM

/-- Round outwards before the exponential to keep certificate arithmetic small. -/
def rounded (b : Box) : Box :=
  ⟨(⌊b.lo * 10^9⌋ : ℚ) / 10^9, (⌈b.hi * 10^9⌉ : ℚ) / 10^9⟩

def finalBox (s : Nat) : Box :=
  let b := rounded (centeredBox s)
  ⟨(expBox b.lo).lo, (expBox b.hi).hi⟩

def numericValid (s : Nat) : Prop :=
  let b := centeredBox s
  let r := rounded b
  r.lo ≤ b.lo ∧ b.hi ≤ r.hi ∧ |r.lo| ≤ 1 ∧ |r.hi| ≤ 1
  deriving Decidable

theorem numeric_valid : ∀ s : Fin 7, numericValid s := by native_decide

lemma factor_enclosed (s : Fin 7) : (finalBox s).Holds (factor s) := by
  obtain ⟨hl, hu, hal, hau⟩ := numeric_valid s
  have h := centered_sound s s.isLt
  have hlr : ((rounded (centeredBox s)).lo : ℝ) ≤ ((centeredBox s).lo : ℝ) := by
    exact_mod_cast hl
  have hur : ((centeredBox s).hi : ℝ) ≤ ((rounded (centeredBox s)).hi : ℝ) := by
    exact_mod_cast hu
  have h' : (rounded (centeredBox s)).Holds (centeredLog s) :=
    ⟨hlr.trans h.1, h.2.trans hur⟩
  exact exp_interval_sound h' hal hau

/-- Easily reviewed, outward decimal enclosures of the exact-real factors. -/
def displayBox (s : Nat) : Box :=
  let centers : List ℚ := [97552770/10^8, 128108361/10^8, 114775497/10^8,
    95641187/10^8, 81578573/10^8, 93243786/10^8, 95828078/10^8]
  ⟨centers[s]! - 1/10^6, centers[s]! + 1/10^6⟩

theorem displayed_enclosures_check : ∀ s : Fin 7,
    (displayBox s).lo ≤ (finalBox s).lo ∧ (finalBox s).hi ≤ (displayBox s).hi := by
  native_decide

theorem exact_factor_enclosures (s : Fin 7) : (displayBox s).Holds (factor s) := by
  have h := factor_enclosed s
  have hc := displayed_enclosures_check s
  have hl : ((displayBox s).lo : ℝ) ≤ ((finalBox s).lo : ℝ) := by exact_mod_cast hc.1
  have hu : ((finalBox s).hi : ℝ) ≤ ((displayBox s).hi : ℝ) := by exact_mod_cast hc.2
  exact ⟨hl.trans h.1, h.2.trans hu⟩

/-- Every shipped value lies farther than 1e-10 from the corresponding
exact-real model factor. Both inequalities are checked as rational arithmetic. -/
theorem separated : ∀ s : Fin 7,
    ((edge[s.val]! + tolerance < (displayBox s).lo) ∨
     ((displayBox s).hi + tolerance < edge[s.val]!)) ∧
    ((rna[s.val]! + tolerance < (displayBox s).lo) ∨
     ((displayBox s).hi + tolerance < rna[s.val]!)) := by native_decide

lemma error_of_separated (b : Box) (x : ℝ) (v e : ℚ) (hx : b.Holds x)
    (hs : v + e < b.lo ∨ b.hi + e < v) : (e : ℝ) < |(v : ℝ) - x| := by
  rcases hs with h | h
  · have hr : (v : ℝ) + (e : ℝ) < (b.lo : ℝ) := by exact_mod_cast h
    have he := le_abs_self (x - (v : ℝ))
    rw [abs_sub_comm] at he
    linarith [hx.1]
  · have hr : (b.hi : ℝ) + (e : ℝ) < (v : ℝ) := by exact_mod_cast h
    have he := le_abs_self ((v : ℝ) - x)
    linarith [hx.2]

theorem R1_exact_real_fails (s : Fin 7) :
    (tolerance : ℝ) < |(edge[s.val]! : ℝ) - factor s| :=
  error_of_separated _ _ _ _ (exact_factor_enclosures s) (separated s).1

theorem R2_exact_real_fails (s : Fin 7) :
    (tolerance : ℝ) < |(rna[s.val]! : ℝ) - factor s| :=
  error_of_separated _ _ _ _ (exact_factor_enclosures s) (separated s).2

/-- Unconditional artifact comparison, using exact decimal rationals. -/
theorem artifact_lengths : edge.length = 7 ∧ rna.length = 7 := by native_decide

theorem R3_first_difference : edge[0]! - rna[0]! = 931142302732627/10^17 := by
  native_decide

theorem R3_all_differ : ∀ s : Fin 7, tolerance < |edge[s.val]! - rna[s.val]!| := by
  native_decide

theorem R3_fails : ¬ (∀ s : Fin 7, |edge[s.val]! - rna[s.val]!| ≤ tolerance) := by
  intro h
  exact (not_le_of_gt (R3_all_differ 0)) (h 0)

#print axioms R1_exact_real_fails
#print axioms R2_exact_real_fails
#print axioms R3_fails
end TMM
