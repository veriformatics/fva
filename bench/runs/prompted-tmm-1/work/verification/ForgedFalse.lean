import Lean
open Lean Elab Command

-- Deliberately bypass elaboration and kernel checking to make a bad .olean.
-- Replay MUST reject this theorem: True.intro is not a proof of False.
set_option debug.skipKernelTC true in
run_elab
  liftM <| addDecl <| .thmDecl {
    name := `forgedFalse
    levelParams := []
    type := mkConst ``False
    value := mkConst ``True.intro
  }
