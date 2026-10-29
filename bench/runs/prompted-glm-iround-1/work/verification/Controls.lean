def Control.badEquality : Prop := (0 : Nat) = 1
def Control.badFalse : Prop := False
theorem Control.good : (0 : Nat) = 0 := rfl
