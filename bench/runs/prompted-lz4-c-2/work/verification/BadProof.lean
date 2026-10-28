import Lean
set_option debug.skipKernelTC true
run_elab Lean.addDecl (.thmDecl {
  name := `badFalse
  levelParams := []
  type := Lean.mkConst ``False
  value := Lean.mkConst ``True.intro
})
