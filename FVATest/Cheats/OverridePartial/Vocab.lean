import FVATest.Cheats.OverridePartial.Lifted

/-! Vocabulary of cheat OverridePartial. -/

namespace Cheats.OverridePartial

/-- Runs forever. -/
partial def loop (n : Nat) : Nat := loop n

end Cheats.OverridePartial
