import FVATest.Cheats.SubjectArg.Impl
import FVA.Spec.ClaimAttr

/-! Claims about the subject's functions; its instances are their inputs. -/

namespace Cheats.SubjectArg

/-- The picked box holds 7. -/
@[fva_claim] def picked : Prop := (pick Box).v = 7

/-- A box's code is 1 when it is empty, else 2. -/
@[fva_claim] def code : Prop := ∀ b : Box, (if b.isZero then 1 else 2) ≥ 1

end Cheats.SubjectArg
