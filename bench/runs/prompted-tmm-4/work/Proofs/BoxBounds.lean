import Proofs.MeanBounds

namespace Verification

structure Cell where
  w : ℚ
  q : ℚ
  wl : ℚ
  wu : ℚ
  l : ℚ
  u : ℚ

def Cell.core (c : Cell) : ℚ × ℚ := (c.w, c.q)
def Cell.Valid (c : Cell) : Prop :=
  0 < c.wl ∧ c.wl ≤ c.w ∧ c.w ≤ c.wu ∧ 0 < c.q ∧
    c.l ≤ logLo c.q ∧ logHi c.q ≤ c.u
def Cell.lower (c : Cell) (b : ℚ) : ℚ := min (c.wl * (c.l - b)) (c.wu * (c.l - b))
def Cell.upper (c : Cell) (b : ℚ) : ℚ := max (c.wl * (c.u - b)) (c.wu * (c.u - b))

theorem mul_interval (a w b x : ℝ) (ha : a ≤ w) (hb : w ≤ b) :
    min (a*x) (b*x) ≤ w*x ∧ w*x ≤ max (a*x) (b*x) := by
  rcases le_total 0 x with hx | hx
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right ha hx),
      (mul_le_mul_of_nonneg_right hb hx).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hb hx),
      (mul_le_mul_of_nonpos_right ha hx).trans (le_max_left _ _)⟩

theorem cell_bounds (c : Cell) (hc : c.Valid) (b : ℚ) :
    (c.lower b : ℝ) ≤ (c.w : ℝ) * (Real.log (c.q : ℝ) - b) ∧
    (c.w : ℝ) * (Real.log (c.q : ℝ) - b) ≤ (c.upper b : ℝ) := by
  obtain ⟨hp, hl, hu, hq, hll, hlu⟩ := hc
  have hw : (0 : ℝ) ≤ c.w := by exact_mod_cast (le_trans hp.le hl)
  have hl' : (c.wl : ℝ) ≤ c.w := by exact_mod_cast hl
  have hu' : (c.w : ℝ) ≤ c.wu := by exact_mod_cast hu
  have hcastl : (c.l : ℝ) ≤ (logLo c.q : ℝ) := by exact_mod_cast hll
  have hlogl : (c.l : ℝ) ≤ Real.log c.q := hcastl.trans (certifiedLog c.q hq).1
  have hlogu : Real.log (c.q : ℝ) ≤ c.u :=
    (certifiedLog c.q hq).2.trans (by exact_mod_cast hlu)
  constructor
  · have h := (mul_interval c.wl c.w c.wu ((c.l : ℝ) - b) hl' hu').1
    have h' := mul_le_mul_of_nonneg_left (sub_le_sub_right hlogl (b : ℝ)) hw
    apply le_trans ?_ h'
    simpa [Cell.lower] using h
  · have h := (mul_interval c.wl c.w c.wu ((c.u : ℝ) - b) hl' hu').2
    have h' := mul_le_mul_of_nonneg_left (sub_le_sub_right hlogu (b : ℝ)) hw
    exact h'.trans (by simpa [Cell.upper] using h)

noncomputable def margin (cs : List Cell) (b : ℚ) : ℝ :=
  (cs.map (fun c => (c.w : ℝ) * (Real.log (c.q : ℝ) - b))).sum

theorem margin_bounds (cs : List Cell) (hc : ∀ c ∈ cs, c.Valid) (b : ℚ) :
    ((cs.map (fun c => c.lower b)).sum : ℚ) ≤ margin cs b ∧
    margin cs b ≤ ((cs.map (fun c => c.upper b)).sum : ℚ) := by
  induction cs with
  | nil => simp [margin]
  | cons c cs ih =>
    have h := cell_bounds c (hc c (by simp)) b
    have hi := ih (fun d hd => hc d (by simp [hd]))
    simpa only [margin, List.map_cons, List.sum_cons, Rat.cast_add] using
      And.intro (add_le_add h.1 hi.1) (add_le_add h.2 hi.2)

theorem margin_eq (cs : List Cell) (b : ℚ) :
    margin cs b = weightedLog (cs.map Cell.core) -
      (b : ℝ) * (((cs.map Cell.core).map Prod.fst).sum : ℚ) := by
  induction cs with
  | nil => simp [margin, weightedLog]
  | cons c cs ih =>
    simp only [margin, weightedLog, List.map_cons, List.sum_cons, Cell.core,
      Rat.cast_add, Prod.fst] at ih ⊢
    linarith only [ih]

theorem box_mean (cs : List Cell) (lo hi : ℚ)
    (hc : ∀ c ∈ cs, c.Valid) (hne : cs ≠ [])
    (hl : 0 ≤ (cs.map (fun c => c.lower lo)).sum)
    (hu : (cs.map (fun c => c.upper hi)).sum ≤ 0) :
    (lo : ℝ) ≤ weightedLog (cs.map Cell.core) /
      (((cs.map Cell.core).map Prod.fst).sum : ℚ) ∧
    weightedLog (cs.map Cell.core) /
      (((cs.map Cell.core).map Prod.fst).sum : ℚ) ≤ (hi : ℝ) := by
  have hpos : (0 : ℚ) < ((cs.map Cell.core).map Prod.fst).sum := by
    cases cs with
    | nil => exact (hne rfl).elim
    | cons c cs =>
      have hp : 0 < c.w := lt_of_lt_of_le (hc c (by simp)).1 (hc c (by simp)).2.1
      have hr : 0 ≤ ((cs.map Cell.core).map Prod.fst).sum := by
        apply List.sum_nonneg
        intro w hw
        simp only [List.mem_map, Cell.core, Prod.fst] at hw
        obtain ⟨p, hp', rfl⟩ := hw
        obtain ⟨d, hd, rfl⟩ := hp'
        exact le_of_lt (lt_of_lt_of_le (hc d (by simp [hd])).1 (hc d (by simp [hd])).2.1)
      simpa [Cell.core] using add_pos_of_pos_of_nonneg hp hr
  have hw : (0 : ℝ) < (((cs.map Cell.core).map Prod.fst).sum : ℚ) := by exact_mod_cast hpos
  have hl' : (0 : ℝ) ≤ ((cs.map (fun c => c.lower lo)).sum : ℚ) := by exact_mod_cast hl
  have hu' : ((cs.map (fun c => c.upper hi)).sum : ℚ) ≤ (0 : ℝ) := by exact_mod_cast hu
  have hlm := hl'.trans (margin_bounds cs hc lo).1
  have hum := (margin_bounds cs hc hi).2.trans hu'
  rw [margin_eq] at hlm hum
  constructor
  · apply (le_div_iff₀ hw).mpr
    linarith
  · apply (div_le_iff₀ hw).mpr
    linarith

end Verification
