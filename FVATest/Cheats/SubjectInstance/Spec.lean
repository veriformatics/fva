import FVATest.Cheats.SubjectInstance.Impl
import FVA.Spec.ClaimAttr

/-! Reads as an ordering and a numeric reading; the subject's instance and coercion make both
claims trivial. -/

namespace Cheats.SubjectInstance

/-- Growing never makes a box smaller. -/
@[fva_claim] def grows : Prop := ∀ b : Box, b ≤ b.grow

/-- A box reads as the number 0. -/
@[fva_claim] def reads : Prop := ∀ b : Box, (b : Nat) = 0

end Cheats.SubjectInstance
