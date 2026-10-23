import FVATest.Cheats.LinkExtra.Lifted

/-! Cheat LinkExtra (U7 E1): a lifted file with a declaration `fva lift` never writes. -/

namespace Cheats.LinkExtra

open Lifted in
/-- The artifact's bytes decode to the lifted module, and the decoding is fine. -/
def decodes : Prop := FVA.Wasm.Decode.decode Lifted.bytes Lifted.len = .ok Lifted.module ∨ fine

end Cheats.LinkExtra
