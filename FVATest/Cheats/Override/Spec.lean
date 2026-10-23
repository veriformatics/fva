import FVATest.Cheats.Override.Lifted
import FVATest.Cheats.Override.Vocab

/-! Cheat Override (U7 E1). -/

namespace Cheats.Override

/-- The artifact's size is its length. -/
def sized : Prop := size Lifted.len = Lifted.len

end Cheats.Override
