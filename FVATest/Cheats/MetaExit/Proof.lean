import FVATest.Cheats.MetaExit.Spec

/-! Proof of the one claim Lean elaborates. -/

theorem Cheats.MetaExit.decodes_holds : Cheats.MetaExit.decodes := Cheats.MetaExit.Lifted.decode_eq
