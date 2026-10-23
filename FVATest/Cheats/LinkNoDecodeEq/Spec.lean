import FVATest.Cheats.LinkNoDecodeEq.Lifted

/-! Cheat LinkNoDecodeEq (U7 E1): the lifted module has no `decode_eq`. -/

namespace Cheats.LinkNoDecodeEq

/-- The artifact's bytes decode to the lifted module. -/
def decodes : Prop := FVA.Wasm.Decode.decode Lifted.bytes Lifted.len = .ok Lifted.module

end Cheats.LinkNoDecodeEq
