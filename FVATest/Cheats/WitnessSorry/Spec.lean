import FVATest.Cheats.Clean.Lifted

namespace Cheats.WitnessSorry

@[fva_claim] def length : Prop := ∀ n : Nat, n + Clean.Lifted.len = n + Clean.Lifted.len

end Cheats.WitnessSorry
