import FVATest.Cheats.MetaInit.Lifted

/-! Cheat MetaInit (U36): `register_option` expands to `initialize`, code every later import runs,
though no listed word appears in the text. -/

register_option cheats.metaInit : Bool := { defValue := false, descr := "cheat MetaInit" }

namespace Cheats.MetaInit

/-- The artifact's bytes decode to the lifted module. -/
@[fva_claim]
def decodes : Prop := FVA.Wasm.Decode.decode Lifted.bytes Lifted.len = .ok Lifted.module

end Cheats.MetaInit
