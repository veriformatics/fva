import FVATest.Cheats.LinkEscape.Lifted

/-! Cheat LinkEscape (U7 E1): the lifted `source` leaves the project by `..`. -/

namespace Cheats.LinkEscape

/-- The artifact's bytes decode to the lifted module. -/
def decodes : Prop := FVA.Wasm.Decode.decode Lifted.bytes Lifted.len = .ok Lifted.module

end Cheats.LinkEscape
