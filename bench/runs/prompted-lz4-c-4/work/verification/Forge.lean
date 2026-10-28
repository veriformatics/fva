-- Deliberately bypass the elaborator's kernel check. These are negative controls,
-- never imported by Proofs. Every replay kernel must reject this module/export.
import Lean
open Lean Elab Command

run_elab do
  let decl := Declaration.thmDecl {
    name := `Forged.falsehood
    levelParams := []
    type := mkConst ``False
    value := mkConst ``True.intro
  }
  match (← getEnv).addDeclCore 0 0 decl none false with
  | .ok env => setEnv env
  | .error _ => throwError "could not construct negative control"
