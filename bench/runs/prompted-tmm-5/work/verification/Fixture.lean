import Lean

theorem fixture_true : True := True.intro
theorem fixture_eq : (0 : Nat) = 0 := rfl
def fixture_false : Prop := False
def fixture_neq : Prop := (0 : Nat) = 1
