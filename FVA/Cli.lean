import FVA.Version

/-! Command dispatch, kept pure so tests can drive it without spawning a process. -/

namespace FVA.Cli

/-- Result of one CLI invocation: text for stdout or stderr, and the exit code. -/
structure Outcome where
  /-- Text for standard output. -/
  out : String := ""
  /-- Text for standard error. -/
  err : String := ""
  /-- Process exit code. -/
  code : UInt32 := 0
deriving Repr, BEq

/-- Top-level help text. -/
def helpText : String :=
  "Usage: fva <command> [options]\n\n" ++
  "FVA checks formal proofs about compiled WebAssembly programs.\n\n" ++
  "Commands:\n" ++
  "  help      Show this help.\n" ++
  "  version   Show the FVA version.\n" ++
  "  decode    Show a summary of each .wasm file that FVA decodes.\n" ++
  "  lift      Write a Lean module that holds a .wasm file and its decoded syntax.\n" ++
  "  difftest  Compare the Lean semantics with wasmtime on the exported functions of .wasm\n" ++
  "            files.\n" ++
  "  trust     Check that a project's claims are proven, about the artifact, with a small\n" ++
  "            spec.\n" ++
  "  explain   Explain a project's claims in plain English and compare them with their intent.\n"

/-- Map command-line arguments to an outcome. -/
def dispatch : List String → Outcome
  | [] | ["help"] | ["--help"] | ["-h"] => { out := helpText }
  | ["version"] | ["--version"] => { out := s!"fva {FVA.version}\n" }
  | cmd :: _ =>
    { err := s!"fva: unknown command \"{cmd}\". Run \"fva help\" to see the commands.\n"
      code := 2 }

end FVA.Cli
