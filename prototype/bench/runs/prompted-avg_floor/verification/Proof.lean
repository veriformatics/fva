import Spec
import Lean.Elab.Tactic.Omega

namespace AvgFloor

theorem floor_spec (a b : Int) :
    2 * ((a + b) / 2) ≤ a + b ∧ a + b < 2 * ((a + b) / 2 + 1) := by
  omega

theorem decoded (a b : Int) :
    run artifact a b = some ((b + a).bmod 4294967296 / 2) := by
  rfl

theorem semantics (a b : Int) :
    run artifact a b = some ((a + b).bmod 4294967296 / 2) := by
  rw [decoded, Int.add_comm b a]

theorem correct_iff (a b : Int) :
    run artifact a b = some ((a + b) / 2) ↔ signed32 (a + b) := by
  rw [semantics]
  simp only [Option.some.injEq, Int.bmod]
  unfold signed32 at *
  split <;> omega

theorem fails_on_overflow (a b : Int)
    (h : a + b < -2147483648 ∨ 2147483648 ≤ a + b) :
    run artifact a b ≠ some ((a + b) / 2) := by
  intro hc
  have := (correct_iff a b).mp hc
  unfold signed32 at this
  omega

theorem positive_counterexample :
    run artifact 2147483647 2147483647 = some (-1) ∧
    ((2147483647 : Int) + 2147483647) / 2 = 2147483647 := by
  decide

theorem negative_counterexample :
    run artifact (-2147483648) (-2147483648) = some 0 ∧
    ((-2147483648 : Int) + (-2147483648)) / 2 = -2147483648 := by
  decide

theorem not_R1 : ¬ R1 := by
  intro h
  have bad := h 2147483647 2147483647 (by unfold signed32; decide) (by unfold signed32; decide)
  rw [positive_counterexample.1, positive_counterexample.2] at bad
  cases bad

theorem not_R2 : ¬ R2 := by
  intro h
  have bad := h 2147483647 2147483647 (by unfold signed32; decide) (by unfold signed32; decide) (by decide)
  rw [positive_counterexample.1, positive_counterexample.2] at bad
  cases bad

end AvgFloor
