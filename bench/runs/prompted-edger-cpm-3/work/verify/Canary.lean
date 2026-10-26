import Init
namespace Canary
theorem trueProof : True := True.intro
theorem zeroEquality : (0 : Nat) = 0 := rfl
def falseType : Prop := False
def unequalType : Prop := (0 : Nat) = 1
end Canary
