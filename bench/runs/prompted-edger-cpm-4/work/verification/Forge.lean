import Lean

-- Deliberately bypass the frontend kernel to produce a well-formed object
-- containing an invalid proof term. Replay must reject it independently.
set_option debug.skipKernelTC true in
run_elab Lean.addDecl (.thmDecl {
  name := `forgedFalse
  levelParams := []
  type := Lean.mkConst ``False
  value := Lean.mkConst ``True.intro
})
