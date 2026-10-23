import FVATest.Cheats.LinkEscape.Spec

/-! Cheat LinkEscape: proofs. -/

theorem Cheats.LinkEscape.decodes_holds : Cheats.LinkEscape.decodes :=
  Cheats.LinkEscape.Lifted.decode_eq
