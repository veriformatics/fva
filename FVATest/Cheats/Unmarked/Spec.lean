import FVATest.Cheats.Unmarked.Lifted

/-! A marked claim beside an unmarked `Prop` that reads as a requirement: PASS (only marked
definitions are claims), and the report lists the unmarked one, since nothing proves it. -/

namespace Cheats.Unmarked

/-- The artifact's bytes decode to the lifted module. -/
@[fva_claim]
def decodes : Prop := FVA.Wasm.Decode.decode Lifted.bytes Lifted.len = .ok Lifted.module

/-- The artifact is empty (false, unmarked: vocabulary, never proven). -/
def empty : Prop := Lifted.len = 0

end Cheats.Unmarked
