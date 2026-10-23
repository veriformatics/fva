import FVATest.Cheats.NativeDecide.Lifted

/-! Cheat NativeDecide (U7 E1). -/

namespace Cheats.NativeDecide

/-- The artifact is small. -/
def small : Prop := Lifted.len < 100

end Cheats.NativeDecide
