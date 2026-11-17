import FVATest.Cheats.MetaExit.Lifted

/-! Cheat MetaExit (U36): `#exit` ends elaboration after the first claim; a reader also sees the
second one, which Lean never checks. -/

namespace Cheats.MetaExit

/-- The artifact's bytes decode to the lifted module. -/
@[fva_claim]
def decodes : Prop := FVA.Wasm.Decode.decode Lifted.bytes Lifted.len = .ok Lifted.module

end Cheats.MetaExit

#exit

namespace Cheats.MetaExit

/-- The lifted function returns its argument. -/
@[fva_claim]
def identity : Prop := ∀ x : BitVec 32, FVA.Spec.Returns Lifted.module "id" [.i32 x] [.i32 x]

end Cheats.MetaExit
