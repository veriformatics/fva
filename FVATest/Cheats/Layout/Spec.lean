import FVATest.Cheats.Layout.Lifted

/-! Cheat Layout (U7 E1). -/

namespace Cheats.Layout

/-- The bytes decode to the lifted module. -/
def decodes : Prop := FVA.Wasm.Decode.decode Lifted.bytes Lifted.len = .ok Lifted.module

theorem decodes_in_spec : decodes := Lifted.decode_eq

end Cheats.Layout
