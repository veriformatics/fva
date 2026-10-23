import FVATest.Cheats.LinkOtherNumeral.Lifted

/-! Cheat LinkOtherNumeral (U7 E1): `decode_eq` speaks of another numeral than `bytes`. -/

namespace Cheats.LinkOtherNumeral

/-- The artifact's bytes decode to the lifted module. -/
def decodes : Prop := FVA.Wasm.Decode.decode Lifted.bytes Lifted.len = .ok Lifted.module

end Cheats.LinkOtherNumeral
