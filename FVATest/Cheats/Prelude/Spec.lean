import FVATest.Cheats.Prelude.Lifted
import FVATest.Cheats.Prelude.Raw

/-! Cheat Prelude (U7 E1). -/

namespace Cheats.Prelude

/-- The bytes decode to the lifted module. -/
def decodes : Prop := FVA.Wasm.Decode.decode Lifted.bytes Lifted.len = .ok Lifted.module

end Cheats.Prelude
