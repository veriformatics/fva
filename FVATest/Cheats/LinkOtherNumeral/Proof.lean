import FVATest.Cheats.LinkOtherNumeral.Spec

/-! Cheat LinkOtherNumeral: proofs. -/

open FVA.Wasm.Decode in
theorem Cheats.LinkOtherNumeral.decodes_holds : Cheats.LinkOtherNumeral.decodes := by
  unfold Cheats.LinkOtherNumeral.decodes; kernel_rfl
