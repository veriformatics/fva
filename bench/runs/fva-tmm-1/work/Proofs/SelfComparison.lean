import Proofs.Selection3

namespace Proofs.Numeric

theorem evalLogs_append (as bs : List (ℚ × Nat)) :
    evalLogs (as ++ bs) = evalLogs as + evalLogs bs := by
  simp [evalLogs, List.map_append, List.sum_append]

theorem pairedLogs (ps : List (Nat × Nat)) (f : Nat × Nat → ℚ)
    (hp : ∀ p ∈ ps, p.1 = p.2) :
    evalLogs (ps.flatMap fun p => [(f p, p.1), (-f p, p.2)]) = 0 := by
  induction ps with
  | nil => simp [evalLogs]
  | cons p ps ih =>
    have he := hp p (by simp)
    have hi := ih (by intro q hq; exact hp q (by simp [hq]))
    rw [List.flatMap_cons, evalLogs_append, hi]
    simp [evalLogs, Rat.cast_neg, he]

theorem raw3_zero : rawLog Witness.matrix 3 3 = 0 := by
  unfold rawLog rawCoeffs
  rewrite [Witness.selected3, Witness.lib3]
  dsimp only
  rewrite [evalLogs_append]
  have hp : ∀ p ∈ Witness.ps3, p.1 = p.2 := by decide +kernel
  have hz := pairedLogs Witness.ps3
    (fun p => weight 1097 1097 p / (Witness.ps3.map (weight 1097 1097)).sum) hp
  rewrite [hz]
  simp [evalLogs]

end Proofs.Numeric
