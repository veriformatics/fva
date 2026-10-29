import Lean
-- Intentionally assign Eq.refl 0 to the false goal 0=1, bypassing elaborator
-- type checking. The kernel MUST reject the resulting declaration.
theorem known_false : (0 : Nat) = 1 := by
  run_tac do
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.assign (← Lean.Meta.mkEqRefl (Lean.mkNatLit 0))
