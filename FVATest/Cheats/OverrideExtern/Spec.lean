import FVATest.Cheats.OverrideExtern.Vocab

/-! Cheat OverrideExtern (U7 E1). -/

namespace Cheats.OverrideExtern

/-- The claim. -/
@[fva_claim] def stable : Prop := add2 Lifted.len 0 = Lifted.len

end Cheats.OverrideExtern
