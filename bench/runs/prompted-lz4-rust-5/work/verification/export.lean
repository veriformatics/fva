import LeanExport.Basic
open Lean
-- Export only the requested roots and their transitive dependencies.
def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := (args.head!).toName }] {} 0
  LeanExport.dumpEnv env (some (args.tail.map String.toName))
