-- Valid seeds for deliberately ill-typed exported proof terms.
theorem controlTrue : True := True.intro
theorem controlFalseIdentity : False → False := fun h => h
theorem controlZero : (0 : Nat) = 0 := rfl
theorem controlOne : (1 : Nat) = 1 := rfl
