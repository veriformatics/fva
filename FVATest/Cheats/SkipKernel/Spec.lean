import FVATest.Cheats.SkipKernel.Lifted

/-! Cheat SkipKernel (U7 E1). -/

namespace Cheats.SkipKernel

/-- The bytes decode to the lifted module. -/
def decodes : Prop := FVA.Wasm.Decode.decode Lifted.bytes Lifted.len = .ok Lifted.module

end Cheats.SkipKernel
