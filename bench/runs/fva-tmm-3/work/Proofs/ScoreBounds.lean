import Proofs.Logs

namespace Proofs

def roundLo (q : ℚ) : ℚ := (⌊q * 1000000⌋ : Int) / 1000000
def roundHi (q : ℚ) : ℚ := ((⌊q * 1000000⌋ : Int) + 1) / 1000000

theorem roundLo_le (q : ℚ) : (roundLo q : ℝ) ≤ (q : ℝ) := by
  have h : roundLo q ≤ q := by
    unfold roundLo
    apply (div_le_iff₀ (by norm_num : (0:ℚ)<1000000)).mpr
    exact Int.floor_le _
  exact_mod_cast h

theorem le_roundHi (q : ℚ) : (q : ℝ) ≤ (roundHi q : ℝ) := by
  have h : q ≤ roundHi q := by
    unfold roundHi
    apply (le_div_iff₀ (by norm_num : (0:ℚ)<1000000)).mpr
    exact (Int.lt_floor_add_one _).le
  exact_mod_cast h

def lowTerm (no nr : Nat) (l : ℚ) (p : Nat × Nat) : ℚ :=
  roundLo (weight no nr p * (logLo p.1 - logHi p.2 + logLo nr - logHi no - l))

def highTerm (no nr : Nat) (u : ℚ) (p : Nat × Nat) : ℚ :=
  roundHi (weight no nr p * (logHi p.1 - logLo p.2 + logHi nr - logLo no - u))

theorem cast_list_sum {α : Type} (ps : List α) (f : α → ℚ) :
    (((ps.map f).sum : ℚ) : ℝ) = (ps.map (fun p => (f p : ℝ))).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp [ih]

theorem sum_weighted_sub (ps : List (Nat × Nat)) (no nr : Nat) (a : ℝ) :
    (ps.map (fun p => (weight no nr p : ℝ) * (logRatio no nr p - a))).sum =
    (ps.map (fun p => (weight no nr p : ℝ) * logRatio no nr p)).sum -
    (ps.map (fun p => (weight no nr p : ℝ))).sum * a := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem weighted_bounds (ps : List (Nat × Nat)) (no nr : Nat) (l u : ℚ)
    (hne : ps ≠ [])
    (hw : ∀ p ∈ ps, (0 : ℚ) < weight no nr p)
    (hp : ∀ p ∈ ps, p.1 ∈ logDomain ∧ p.2 ∈ logDomain)
    (hno : no ∈ logDomain) (hnr : nr ∈ logDomain)
    (hl : 0 ≤ (ps.map (lowTerm no nr l)).sum)
    (hu : (ps.map (highTerm no nr u)).sum ≤ 0) :
    (l : ℝ) ≤ (ps.map (fun p => (weight no nr p : ℝ) * logRatio no nr p)).sum /
      (ps.map (fun p => (weight no nr p : ℝ))).sum ∧
    (ps.map (fun p => (weight no nr p : ℝ) * logRatio no nr p)).sum /
      (ps.map (fun p => (weight no nr p : ℝ))).sum ≤ (u : ℝ) := by
  have hd : 0 < (ps.map (fun p => (weight no nr p : ℝ))).sum := by
    apply List.sum_pos
    · intro v hv
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
      exact_mod_cast hw p hp
    · simpa using hne
  have hlo : ∀ p ∈ ps, (lowTerm no nr l p : ℝ) ≤
      (weight no nr p : ℝ) * (logRatio no nr p - (l : ℝ)) := by
    intro p hmem
    have hp1 := log_bounds p.1 (hp p hmem).1
    have hp2 := log_bounds p.2 (hp p hmem).2
    have hn := log_bounds no hno
    have hr := log_bounds nr hnr
    have hm : ((logLo p.1 - logHi p.2 + logLo nr - logHi no - l : ℚ) : ℝ) ≤
        logRatio no nr p - (l : ℝ) := by
      push_cast
      unfold logRatio
      linarith
    have hwr : (0 : ℝ) ≤ weight no nr p := by exact_mod_cast (hw p hmem).le
    exact (roundLo_le _).trans (by simpa using mul_le_mul_of_nonneg_left hm hwr)
  have hhi : ∀ p ∈ ps, (weight no nr p : ℝ) * (logRatio no nr p - (u : ℝ)) ≤
      (highTerm no nr u p : ℝ) := by
    intro p hmem
    have hp1 := log_bounds p.1 (hp p hmem).1
    have hp2 := log_bounds p.2 (hp p hmem).2
    have hn := log_bounds no hno
    have hr := log_bounds nr hnr
    have hm : logRatio no nr p - (u : ℝ) ≤
        ((logHi p.1 - logLo p.2 + logHi nr - logLo no - u : ℚ) : ℝ) := by
      push_cast
      unfold logRatio
      linarith
    have hwr : (0 : ℝ) ≤ weight no nr p := by exact_mod_cast (hw p hmem).le
    calc
      _ ≤ ((weight no nr p * (logHi p.1 - logLo p.2 + logHi nr - logLo no - u) : ℚ) : ℝ) := by
        simpa using mul_le_mul_of_nonneg_left hm hwr
      _ ≤ (highTerm no nr u p : ℝ) := le_roundHi _
  have hslo := List.sum_le_sum hlo
  have hshi := List.sum_le_sum hhi
  rw [← cast_list_sum] at hslo hshi
  have hlR : (0 : ℝ) ≤ ((ps.map (lowTerm no nr l)).sum : ℚ) := by exact_mod_cast hl
  have huR : (((ps.map (highTerm no nr u)).sum : ℚ) : ℝ) ≤ 0 := by exact_mod_cast hu
  rw [sum_weighted_sub] at hslo hshi
  rw [le_div_iff₀ hd, div_le_iff₀ hd]
  constructor <;> nlinarith

end Proofs
