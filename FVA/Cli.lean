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
  "  init      Create a verification project with FVA in it.\n" ++
  "  version   Show the FVA version.\n" ++
  "  decode    Show a summary of each .wasm file that FVA decodes.\n" ++
  "  lift      Write a Lean module that holds a .wasm file and its decoded syntax.\n" ++
  "  difftest  Compare the Lean semantics with wasmtime on the exported functions of .wasm\n" ++
  "            files.\n" ++
  "  trust     Check that a project's claims are proven, about the artifact, with a small\n" ++
  "            spec.\n" ++
  "  explain   Explain a project's claims in plain English and compare them with their intent.\n" ++
  "  blob      Write a Lean module that holds the bytes of a file.\n" ++
  "  certify   Write a certificate: a claim that an output file stands in a relation to an\n" ++
  "            input file, and its proof by a verified checker.\n\n" ++
  "Run \"fva <command> --help\" to see the arguments and options of a command.\n"

/-- Usage text of each command that takes arguments (`fva <command> --help`); `difftest`
prints its own. -/
def usage : String → Option String
  | "decode" => some <|
    "Usage: fva decode <file.wasm>...\n\n" ++
    "Show a summary of each .wasm file that FVA decodes.\n"
  | "lift" => some <|
    "Usage: fva lift <file.wasm> <out.lean> --ns <Namespace>\n\n" ++
    "Write a Lean module that holds the bytes of the .wasm file, its decoded syntax and the\n" ++
    "proof that the decoder gives this syntax. Run the command in the project root, and give\n" ++
    "the .wasm path relative to the project root, without `..`.\n"
  | "blob" => some <|
    "Usage: fva blob <file> <out.lean> --ns <Namespace>\n\n" ++
    "Write a Lean module that holds the bytes of the file. Run the command in the project\n" ++
    "root, and give the path relative to the project root, without `..`.\n"
  | "trust" => some <|
    "Usage: fva trust <project> --spec-module <M> [options]\n\n" ++
    "Build the project, then check that each claim of the spec module is proven, about the\n" ++
    "artifact, with a small spec. The report shows what you must read.\n\n" ++
    "Options:\n" ++
    "  --spec-module M       The module that states the claims (required).\n" ++
    "  --root-module R       The module that imports the proofs (default: the spec module's\n" ++
    "                        parent, for example Demo for Demo.Spec).\n" ++
    "  --subject M           Count the Lean module M as a subject. You can give this option\n" ++
    "                        more than once.\n" ++
    "  --paranoid            Replay the proofs with every bundled kernel.\n" ++
    "  --surface-budget N    Fail when the review surface has more than N code lines.\n" ++
    "  --json                Write the report as JSON.\n" ++
    "  --kernel-limit S      Stop a kernel replay after S seconds (default 1200).\n" ++
    "  --canary-limit S      Stop a canary check after S seconds (default 60).\n\n" ++
    "Exit status: 0 when the verdict is PASS, 1 when it is FAIL, 2 for a usage or setup\n" ++
    "error.\n"
  | "explain" => some <|
    "Usage: fva explain <project> --spec-module <M> [options]\n\n" ++
    "Explain each claim in plain English and compare the explanation with the claim's intent\n" ++
    "(its docstring). The text is saved beside the spec module and shown again without a\n" ++
    "model call. A signed-in codex CLI writes the text.\n\n" ++
    "Options:\n" ++
    "  --spec-module M   The module that states the claims (required).\n" ++
    "  --root-module R   The module that imports the proofs.\n" ++
    "  --model M         Use the model M.\n" ++
    "  --effort E        Use the reasoning effort E (default medium).\n" ++
    "  --force           Write the text again.\n" ++
    "  --json            Write the result as JSON.\n\n" ++
    "Exit status: 0 when the trust verdict is PASS, each claim matches its intent and the\n" ++
    "saved text is current, 1 otherwise, 2 for a usage error.\n"
  | "certify" => some <|
    "Usage: fva certify <project> --relation R --input I --output O --ns Ns [options]\n\n" ++
    "Write a certificate: a claim that the output file stands in the relation R to the input\n" ++
    "file, and its proof by the verified checker of R. Then run lake build and fva trust.\n" ++
    "Give the files relative to the project, without `..`.\n\n" ++
    "Options:\n" ++
    "  --relation-module M   The module that defines R (needed for a relation outside FVA).\n" ++
    "  --sound-module P      The module that proves R's checker sound (same condition).\n\n" ++
    "Exit status: 0 when the files are written, 2 for a usage error or a missing file.\n"
  | "init" => some <|
    "Usage: fva init <directory> [--lib Name] [--wasm file.wasm]\n\n" ++
    "Create a verification project: FVA vendored in fva/, a lakefile, and templates for the\n" ++
    "spec and the proofs. With --wasm, also the artifact and its lifted module.\n\n" ++
    "Options:\n" ++
    "  --lib Name         The library name, a Lean module name (default Verified).\n" ++
    "  --wasm file.wasm   Copy this artifact into the project and lift it.\n\n" ++
    "Exit status: 0 when the project is written, 2 for a usage or setup error.\n"
  | _ => none

/-- Map command-line arguments to an outcome. -/
def dispatch : List String → Outcome
  | [] | ["help"] | ["--help"] | ["-h"] => { out := helpText }
  | ["version"] | ["--version"] => { out := s!"fva {FVA.version}\n" }
  | ["help", cmd] | [cmd, "--help"] | [cmd, "-h"] => match usage cmd with
    | some u => { out := u }
    | none => if bare.contains cmd then { out := helpText } else unknown cmd
  | cmd :: _ => match usage cmd with
    | some u => { err := s!"fva {cmd}: wrong arguments.\n\n{u}", code := 2 }
    | none => if bare.contains cmd then { err := helpText, code := 2 } else unknown cmd
where
  /-- Commands without arguments. -/
  bare : List String := ["help", "version"]
  /-- An unknown command: name it and point at the command list. -/
  unknown (cmd : String) : Outcome :=
    { err := s!"fva: unknown command \"{cmd}\". Run \"fva help\" to see the commands.\n"
      code := 2 }

end FVA.Cli
