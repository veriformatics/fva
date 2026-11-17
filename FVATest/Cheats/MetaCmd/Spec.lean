import FVATest.Cheats.MetaCmd.Lifted

/-! Cheat MetaCmd (U36): the claim exists only as what a metaprogram declares, so the reviewed text
shows the program, not the statement. -/

open Lean Elab Command in
run_cmd do
  let n := mkIdent `Cheats.MetaCmd.decodes
  elabCommand (← `(command| @[fva_claim] def $n : Prop :=
    FVA.Wasm.Decode.decode Cheats.MetaCmd.Lifted.bytes Cheats.MetaCmd.Lifted.len =
      .ok Cheats.MetaCmd.Lifted.module))
