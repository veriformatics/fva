import FVATest.Cheats.Axiom.Lifted

/-! Cheat Axiom (U7 E1). -/

namespace Cheats.Axiom

/-- The bytes decode to the lifted module. -/
def decodes : Prop := FVA.Wasm.Decode.decode Lifted.bytes Lifted.len = .ok Lifted.module

end Cheats.Axiom
