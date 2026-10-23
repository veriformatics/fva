import FVATest.Cheats.Syntax.Lifted
import FVATest.Cheats.Syntax.Vocab

/-! Cheat Syntax (U7 E1). -/

namespace Cheats.Syntax

/-- The bytes decode to the lifted module. -/
def decodes : Prop := ⟪FVA.Wasm.Decode.decode Lifted.bytes Lifted.len = .ok Lifted.module⟫

end Cheats.Syntax
