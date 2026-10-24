import FVA.Tool.Blob

/-!
# `fva certify`: write a certificate project for one input/output pair

`fva certify <project> --relation R --input I --output O --ns Ns [--relation-module M]
[--sound-module P]` writes, under the project: the two blob modules `Ns.In`, `Ns.Out`
(`fva blob`), the claim `Ns.Spec` (`def claim : Prop := Accepted R In.blob Out.blob`, which
imports only `M`, the reviewed relation), the proof `Ns.Proof` (`R.check_sound` applied to the
kernel's evaluation of `R.check`, from `P`), and the root `Ns` importing the proof. Every file is
generated, so nothing per certificate is trusted but the kernel and the relation; the verdict
comes from `lake build` and `fva trust`, never from this command.
-/

namespace FVA.Tool.Certify

/-- FVA's own relations: name, the module defining it, the module proving its checker sound. -/
def builtins : List (String × String × String) :=
  [("FVA.Cert.SortedPerm", "FVA.Spec.Rel.Sort", "FVA.Proof.Cert.Sort"),
   ("FVA.Cert.Compiled", "FVA.Spec.Rel.Compile", "FVA.Proof.Cert.Compile")]

/-- The source file of module `m` under `root`. -/
def modFile (root : System.FilePath) (m : String) : System.FilePath :=
  (root / ("/".intercalate (m.splitOn "."))).addExtension "lean"

/-- The claim module. -/
def specFile (ns rel relMod inSrc outSrc : String) : String :=
  s!"import {relMod}\nimport {ns}.In\nimport {ns}.Out\n\n" ++
  "/-! Certificate claim written by `fva certify`. -/\n\n" ++
  s!"namespace {ns}\n\n" ++
  s!"/-- The bytes of\n`{outSrc}`\nstand in relation `{rel}` to the bytes of\n`{inSrc}`. -/\n" ++
  s!"def claim : Prop := FVA.Cert.Accepted {rel} In.blob Out.blob\n\n" ++
  s!"end {ns}\n"

/-- The proof module: the checker's soundness theorem on the kernel's evaluation of the check. -/
def proofFile (ns rel soundMod : String) : String :=
  s!"import {ns}.Spec\nimport {soundMod}\n\n" ++
  "/-! Certificate proof written by `fva certify`: the kernel evaluates the checker. -/\n\n" ++
  s!"namespace {ns}\n\n" ++
  s!"theorem claim_holds : claim :=\n  {rel}.check_sound In.blob Out.blob (by kernel_rfl)\n\n" ++
  s!"end {ns}\n"

/-- Parsed options. -/
structure Opts where
  dir : String := ""
  relation : String := ""
  relationModule : Option String := none
  soundModule : Option String := none
  input : String := ""
  output : String := ""
  ns : String := ""

/-- Parse options (`dir` first). -/
def parse (o : Opts) : List String → Except String Opts
  | [] =>
    if o.dir.isEmpty || o.relation.isEmpty || o.input.isEmpty || o.output.isEmpty ||
        o.ns.isEmpty then
      .error "need <project> --relation R --input I --output O --ns Ns"
    else .ok o
  | "--relation" :: r :: rest => parse { o with relation := r } rest
  | "--relation-module" :: m :: rest => parse { o with relationModule := some m } rest
  | "--sound-module" :: m :: rest => parse { o with soundModule := some m } rest
  | "--input" :: f :: rest => parse { o with input := f } rest
  | "--output" :: f :: rest => parse { o with output := f } rest
  | "--ns" :: n :: rest => parse { o with ns := n } rest
  | a :: rest =>
    if a.startsWith "--" then .error s!"unknown option {a}"
    else if o.dir.isEmpty then parse { o with dir := a } rest
    else .error s!"unexpected argument {a}"

/-- A path relative to the project, without `..` (`fva trust` reads the file back through it). -/
def relative (p : String) : Bool :=
  let f : System.FilePath := p
  !f.isAbsolute && !f.components.contains ".."

/-- `fva certify`: rc 0 = files written, 2 = usage or a missing file. -/
def main (argv : List String) : IO UInt32 := do
  let o ← match parse {} argv with
    | .ok o => pure o
    | .error e =>
      IO.eprintln s!"fva certify: {e}. Run \"fva certify --help\" to see the options."
      return 2
  let known := builtins.find? (·.1 == o.relation)
  let some relMod := o.relationModule <|> known.map (·.2.1)
    | IO.eprintln s!"fva certify: give --relation-module for {o.relation}"; return 2
  let some soundMod := o.soundModule <|> known.map (·.2.2)
    | IO.eprintln s!"fva certify: give --sound-module for {o.relation}"; return 2
  unless relative o.input && relative o.output do
    IO.eprintln "fva certify: give --input and --output relative to the project, without `..`"
    return 2
  let root : System.FilePath := o.dir
  let read (f : String) : IO (Option ByteArray) := do
    try return some (← IO.FS.readBinFile (root / f)) catch _ => return none
  let some ib ← read o.input | IO.eprintln s!"fva certify: cannot read {o.input}"; return 2
  let some ob ← read o.output | IO.eprintln s!"fva certify: cannot read {o.output}"; return 2
  let write (m text : String) : IO Unit := do
    let f := modFile root m
    if let some d := f.parent then IO.FS.createDirAll d
    IO.FS.writeFile f text
  write s!"{o.ns}.In" (FVA.Tool.Blob.file s!"{o.ns}.In" ib o.input)
  write s!"{o.ns}.Out" (FVA.Tool.Blob.file s!"{o.ns}.Out" ob o.output)
  write s!"{o.ns}.Spec" (specFile o.ns o.relation relMod o.input o.output)
  write s!"{o.ns}.Proof" (proofFile o.ns o.relation soundMod)
  write o.ns s!"import {o.ns}.Proof\n"
  IO.println "Certificate files written; acceptance requires fva trust."
  return 0

end FVA.Tool.Certify
