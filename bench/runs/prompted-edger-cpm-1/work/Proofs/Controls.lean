import Init
namespace Controls
-- Positive seed. The check script changes only this theorem's declared type,
-- retaining its Eq.refl proof, to each of the two known false propositions.
theorem valid : (0 : Nat) = 0 := rfl
def falseEquality : Prop := (0 : Nat) = 1
def falseOrder : Prop := (1 : Nat) < 0
end Controls
