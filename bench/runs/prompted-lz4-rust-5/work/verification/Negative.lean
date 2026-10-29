import Init
namespace Negative
-- Both target types are false. They are definitions, not assumed axioms.
def unequal : Prop := (0 : Nat) = 1
def bottom : Prop := False
theorem good : (0 : Nat) = 0 := rfl
end Negative
