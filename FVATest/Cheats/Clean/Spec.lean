import FVATest.Cheats.Clean.Lifted

/-! Clean cheat-suite project: one honest claim about the lifted `id.wasm`. -/

namespace Cheats.Clean

/-- The artifact's bytes decode to the lifted module. -/
def decodes : Prop := FVA.Wasm.Decode.decode Lifted.bytes Lifted.len = .ok Lifted.module

end Cheats.Clean
