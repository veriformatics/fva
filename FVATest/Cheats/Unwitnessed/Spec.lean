import FVATest.Cheats.Unwitnessed.Impl
import FVA.Spec.ClaimAttr

namespace Cheats.Unwitnessed

@[fva_claim] def impossible : Prop := ∀ x : Nat, x < 0 → identity x = 1

end Cheats.Unwitnessed
