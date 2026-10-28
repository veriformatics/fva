import LeanExport.Basic
open Lean
unsafe def main (args : List String) : IO Unit := do
  let mod :: roots := args | throw (IO.userError "expected module and theorem names")
  if roots.isEmpty then throw (IO.userError "expected nonempty theorem list")
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := mod.toName}] {} 0
  LeanExport.dumpEnv env (some (roots.map String.toName))
