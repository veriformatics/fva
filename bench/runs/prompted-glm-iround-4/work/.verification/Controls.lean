import Init
def falseType : Prop := False
def unequalType : Prop := (0 : Nat) = 1
theorem trueProof : True := True.intro
theorem equalityProof : (0 : Nat) = 0 := rfl
