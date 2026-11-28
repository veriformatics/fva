import FVATest.Cheats.Unwitnessed.Spec

namespace Cheats.Unwitnessed

theorem impossible_holds : impossible := fun x h => (Nat.not_lt_zero x h).elim

end Cheats.Unwitnessed
