import FVATest.Cheats.LinkSource.Lifted

/-! Cheat LinkSource (U7 E1). -/

namespace Cheats.LinkSource

/-- The bytes decode to the lifted module. -/
@[fva_claim]
def decodes : Prop := FVA.Wasm.Decode.decode Lifted.bytes Lifted.len = .ok Lifted.module

end Cheats.LinkSource
