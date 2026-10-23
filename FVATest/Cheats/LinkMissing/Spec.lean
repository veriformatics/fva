import FVATest.Cheats.LinkMissing.Lifted

/-! Cheat LinkMissing (U7 E1). -/

namespace Cheats.LinkMissing

/-- The bytes decode to the lifted module. -/
def decodes : Prop := FVA.Wasm.Decode.decode Lifted.bytes Lifted.len = .ok Lifted.module

end Cheats.LinkMissing
