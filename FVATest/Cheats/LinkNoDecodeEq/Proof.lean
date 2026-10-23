import FVATest.Cheats.LinkNoDecodeEq.Spec

/-! Cheat LinkNoDecodeEq: proofs. -/

open FVA.Wasm.Decode in
theorem Cheats.LinkNoDecodeEq.decodes_holds : Cheats.LinkNoDecodeEq.decodes := by
  unfold Cheats.LinkNoDecodeEq.decodes; kernel_rfl
