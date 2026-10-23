import FVATest.Cheats.Clean.Spec

/-! Proof of the clean claim. -/

theorem Cheats.Clean.decodes_holds : Cheats.Clean.decodes := Cheats.Clean.Lifted.decode_eq
