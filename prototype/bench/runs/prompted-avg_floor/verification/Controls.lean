namespace Controls
theorem truth : True := True.intro
theorem falsity_type : False → False := fun h => h
theorem arithmetic : (0 : Nat) = 0 := rfl
theorem one : (1 : Nat) = 1 := rfl
end Controls
