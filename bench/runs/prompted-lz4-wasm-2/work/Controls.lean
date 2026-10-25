import Init

namespace Controls
theorem truth : True := True.intro
def falseType : Prop := False
theorem equal : (0 : Nat) = 0 := rfl
def unequal : Prop := (0 : Nat) = 1
end Controls
