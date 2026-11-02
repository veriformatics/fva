import FVATest.Cheats.Unmarked.Spec

/-! Proof of the marked claim. -/

theorem Cheats.Unmarked.decodes_holds : Cheats.Unmarked.decodes :=
  Cheats.Unmarked.Lifted.decode_eq
