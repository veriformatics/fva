namespace NegativeControls
-- Valid statements that allow well-formed, type-incorrect export mutations.
def falseEquality : Prop := (0 : Nat) = 1
def falseArithmetic : Prop := (2 : Nat) + 2 = 5
theorem control : (0 : Nat) = 0 := rfl

end NegativeControls
