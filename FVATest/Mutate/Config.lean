import Lean

/-!
# Mutation-check configuration (`FVATest/Mutate/config.json`, contract S1 + K3)
-/

namespace FVA.Mutate

open Lean

/-- One test command (stage `test:<name>`). -/
structure TestCfg where
  /-- Stage name suffix. -/
  name : String
  /-- argv, run from the tree root; rc 0 pass, 1 assertion failure, other = infrastructure. -/
  cmd : List String
  /-- Modules whose import closures the command executes (its executables' roots). -/
  exeRoots : List String
  /-- Scripts, helper scripts and data the command reads (files or directories). -/
  files : List String
deriving FromJson, ToJson, Inhabited

/-- A scope group (contract S1) and its stage order (K3). -/
structure GroupCfg where
  /-- Group name. -/
  name : String
  /-- Directories (or files) whose definitions are mutated. -/
  dirs : List String := []
  /-- Helper group: the groups whose definition values are traced. -/
  reachFrom : List String := []
  /-- Helper group: module-name prefix of the modules whose reached definitions are mutated. -/
  within : String := ""
  /-- Stages: `module`, `proofs`, `exes`, `test:<name>`. -/
  stages : List String
deriving FromJson, ToJson, Inhabited

/-- The whole configuration. -/
structure Config where
  /-- Directories + files holding the package's modules. -/
  srcRoots : List String
  /-- Path prefixes left out of the module graph (tooling, fixtures). -/
  exclude : List String := []
  /-- Modules defining `main` (never imported together). -/
  exeRoots : List String
  /-- Modules whose closures hold the proofs (stage `proofs`). -/
  proofRoots : List String
  /-- Lake executables built by stage `exes`. -/
  exes : List String
  /-- Paths shared read-only by every worker (integrity-checked). -/
  shared : List String
  /-- Tool binaries the tests call (hashed into the manifest). -/
  tools : List String := []
  /-- Commands whose output enters the manifest (tool versions). -/
  versions : List (List String) := []
  /-- Files every digest covers. -/
  keyFiles : List String
  /-- Test commands. -/
  tests : List TestCfg
  /-- Scope groups. -/
  groups : List GroupCfg
  /-- Workers; 0 = cores ÷ 2. -/
  workers : Nat := 0
  /-- Committed results table. -/
  results : String
  /-- Committed rulings. -/
  rulings : String
  /-- Local cache + run directory. -/
  cacheDir : String
  /-- Rows replayed by the full-mode spot-check. -/
  spotChecks : Nat := 3
  /-- Floor of every stage limit, seconds (K6). -/
  minLimit : Nat := 60
deriving FromJson, ToJson, Inhabited

/-- Load a configuration file. -/
def Config.load (path : System.FilePath) : IO Config := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  IO.ofExcept (fromJson? j)

end FVA.Mutate
