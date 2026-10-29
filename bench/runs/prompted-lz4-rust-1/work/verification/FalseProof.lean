import Lean
open Lean Elab Command

-- Intentionally bypass elaborator checking to create a poisoned .olean.
-- This module is NEVER imported by Proofs. Each replay must reject it.
set_option debug.skipKernelTC true
elab "inject_false_proof" : command => liftCoreM do
  addDecl (.thmDecl { name := `knownFalse, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro })
inject_false_proof
