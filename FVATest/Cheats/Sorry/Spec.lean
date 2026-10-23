import FVATest.Cheats.Sorry.Lifted

/-! Cheat Sorry (U7 E1). -/

namespace Cheats.Sorry

/-- The bytes decode to the lifted module. -/
def decodes : Prop := FVA.Wasm.Decode.decode Lifted.bytes Lifted.len = .ok Lifted.module

end Cheats.Sorry
