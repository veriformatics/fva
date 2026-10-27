import Lean
import LeanExport.Basic

open Lean
unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let roots := args.map String.toName
  withImportModules #[{ module := `Proofs }] {} fun env => do
    LeanExport.dumpEnv env (some roots)
