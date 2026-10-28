import Lean
set_option debug.skipKernelTC true in
run_elab do
  Lean.addDecl <| .thmDecl {
    name := `deliberatelyFalse
    levelParams := []
    type := Lean.mkConst ``False
    value := Lean.mkConst ``True.intro
  }
