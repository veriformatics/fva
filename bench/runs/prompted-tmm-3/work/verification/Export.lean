import LeanExport.Basic
open Lean
-- Dependency-closed export of explicit roots; never export an empty environment.
def main (args : List String) : IO Unit := do
  let modName := (args.head!).toName
  let roots := (args.drop 1).map String.toName
  if roots.isEmpty then throw (IO.userError "Explicit proof roots required")
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := modName}] {} 0
  for n in roots do
    if !env.contains n then throw (IO.userError s!"Missing root {n}")
  LeanExport.dumpEnv env (some roots)
