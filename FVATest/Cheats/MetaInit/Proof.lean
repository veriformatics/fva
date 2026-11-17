import FVATest.Cheats.MetaInit.Spec

/-! Proof of the clean claim beside the initializer. -/

theorem Cheats.MetaInit.decodes_holds : Cheats.MetaInit.decodes := Cheats.MetaInit.Lifted.decode_eq
