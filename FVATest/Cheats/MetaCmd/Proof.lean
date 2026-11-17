import FVATest.Cheats.MetaCmd.Spec

/-! Proof of the claim the metaprogram declares. -/

theorem Cheats.MetaCmd.decodes_holds : Cheats.MetaCmd.decodes := Cheats.MetaCmd.Lifted.decode_eq
