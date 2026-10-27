import Lean
 theorem verificationArithmeticControl : (37 : Nat) + 5 = 42 := rfl
 theorem verificationFalseControl : False → False := fun h => h
