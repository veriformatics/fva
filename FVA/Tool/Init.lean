import Lean.Data.Json
import FVA.Tool.Lift

/-!
# `fva init`: a new verification project with FVA vendored

`fva init <dir> [--lib Name] [--wasm file.wasm]` writes a Lake project: FVA's Lean package copied
into `fva/` (its library, CLI and canary tables, at this binary's version), a lakefile requiring
it by path (Mathlib comes with it, pinned as FVA pins it), a manifest pinning every package as
FVA's does (so it builds offline once Mathlib's oleans are cached), and a library with a claims
module (`Spec`), a proofs module (`Proof`) and, with `--wasm`, the lifted artifact (`Lifted`).
`fva trust` later recognizes the vendored files by content (`baseManifest`), so an edited copy
enters the review surface.
-/

namespace FVA.Tool.Init

open Lean

/-- Files and directories of the FVA package that a project vendors (relative to FVA's root). -/
def vendored : List String :=
  ["FVA", "FVA.lean", "Main.lean", "lean-toolchain", "lake-manifest.json", "trust/canaries",
   "scripts/fetch-tools", "scripts/fetch-canaries", "LICENSE", "README.md", "AGENT.md"]

/-- The vendored package's lakefile: FVA's library and CLI, nothing of its test suite. -/
def fvaLakefile : String :=
  "name = \"fva\"\nversion = \"0.1.0\"\ndefaultTargets = [\"FVA\", \"fva\"]\n" ++
  "allowNonModules = true\n\n" ++
  "[leanOptions]\nautoImplicit = false\nrelaxedAutoImplicit = false\n\n" ++
  "[[require]]\nname = \"mathlib\"\n" ++
  "git = \"https://github.com/leanprover-community/mathlib4\"\nrev = \"v4.35.0\"\n\n" ++
  "[[lean_lib]]\nname = \"FVA\"\n\n[[lean_exe]]\nname = \"fva\"\nroot = \"Main\"\n"

/-- The project's lakefile. -/
def projectLakefile (name lib : String) : String :=
  s!"name = \"{name}\"\ndefaultTargets = [\"{lib}\"]\nallowNonModules = true\n\n" ++
  "[leanOptions]\nautoImplicit = false\nrelaxedAutoImplicit = false\n\n" ++
  "[[require]]\nname = \"fva\"\npath = \"fva\"\n\n" ++ s!"[[lean_lib]]\nname = \"{lib}\"\n"

/-- The project's manifest: the vendored FVA by path, then FVA's own pins, inherited. -/
def projectManifest (name : String) (fvaManifest : Json) : Json :=
  let pkgs := ((fvaManifest.getObjValD "packages").getArr?.toOption.getD #[]).map fun p =>
    p.setObjVal! "inherited" true
  let fva := Json.mkObj [("type", "path"), ("scope", ""), ("name", "fva"),
    ("manifestFile", "lake-manifest.json"), ("inherited", false), ("dir", "./fva"),
    ("configFile", "lakefile.toml")]
  Json.mkObj [("version", fvaManifest.getObjValD "version"), ("packagesDir", ".lake/packages"),
    ("packages", Json.arr (#[fva] ++ pkgs)), ("name", toJson name), ("lakeDir", ".lake")]

/-- The claims module template. -/
def specFile (lib : String) (lifted : Bool) : String :=
  (if lifted then s!"import {lib}.Lifted\n" else "") ++ "import FVA.Spec.CAbi\n\n" ++
  "/-! Claims: `Prop`-valued definitions about the artifact, read by a reviewer. Import only\n" ++
  "FVA's specs and the lifted artifact here; proofs go to `Proof.lean`. -/\n\n" ++
  s!"namespace {lib}\n\nopen FVA.Wasm FVA.Wasm.Exec\n\n" ++
  "-- Example: `def answer : Prop := Returns Lifted.module \"f\" [.i32 1] [.i32 2]`\n\n" ++
  s!"end {lib}\n"

/-- The proofs module template. -/
def proofFile (lib : String) : String :=
  s!"import {lib}.Spec\nimport FVA.Proof.Lib\n\n" ++
  "/-! Proofs: one theorem per claim, typed by the claim constant (`theorem answer_holds :\n" ++
  "answer := …`). Nobody reads this file; `fva trust` checks it. -/\n\n" ++
  s!"namespace {lib}\n\nopen FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref\n\nend {lib}\n"

/-- Copy `src` (a file or a directory tree) to `dst`. -/
partial def copyTree (src dst : System.FilePath) : IO Unit := do
  if ← src.isDir then
    IO.FS.createDirAll dst
    for e in ← src.readDir do copyTree e.path (dst / e.fileName)
  else
    if let some d := dst.parent then IO.FS.createDirAll d
    IO.FS.writeBinFile dst (← IO.FS.readBinFile src)

/-- Parsed options. -/
structure Opts where
  dir : String := ""
  lib : String := "Verified"
  wasm : Option String := none

/-- Parse options (`dir` first). -/
def parse (o : Opts) : List String → Except String Opts
  | [] => if o.dir.isEmpty then .error "no project directory given" else .ok o
  | "--lib" :: l :: r => parse { o with lib := l } r
  | "--wasm" :: f :: r => parse { o with wasm := some f } r
  | a :: r =>
    if a.startsWith "--" then .error s!"unknown option {a}"
    else if o.dir.isEmpty then parse { o with dir := a } r
    else .error s!"unexpected argument {a}"

/-- `fva init`: rc 0 = project written, 2 = usage or setup. -/
def main (fvaRoot : System.FilePath) (argv : List String) : IO UInt32 := do
  let o ← match parse {} argv with
    | .ok o => pure o
    | .error e =>
      IO.eprintln s!"fva init: {e}. Run \"fva init --help\" to see the options."
      return 2
  unless o.lib.front.isUpper && o.lib.all fun c => c.isAlphanum || c == '_' do
    IO.eprintln s!"fva init: --lib must be a module name such as Verified, got {o.lib}"
    return 2
  let dir : System.FilePath := o.dir
  let name := (dir.fileName.getD "project").toLower.map fun c => if c.isAlphanum then c else '_'
  -- the project requires the vendored package `fva`; a project of the same name cannot
  if name == "fva" then
    IO.eprintln s!"fva init: a project in a directory named {dir.fileName.getD ""} would have \
      the package name of the FVA package it requires. Choose another directory name."
    return 2
  if ← dir.pathExists then
    unless (← dir.readDir).isEmpty do
      IO.eprintln s!"fva init: {dir} exists and is not empty"
      return 2
  for f in vendored do
    let src := fvaRoot / f
    if ← src.pathExists then copyTree src (dir / "fva" / f)
  IO.FS.writeFile (dir / "fva" / "lakefile.toml") fvaLakefile
  IO.FS.writeFile (dir / "lakefile.toml") (projectLakefile name o.lib)
  IO.FS.writeFile (dir / "lean-toolchain") (← IO.FS.readFile (fvaRoot / "lean-toolchain"))
  let fm ← IO.ofExcept (Json.parse (← IO.FS.readFile (fvaRoot / "lake-manifest.json")))
  IO.FS.writeFile (dir / "lake-manifest.json") ((projectManifest name fm).pretty ++ "\n")
  IO.FS.writeFile (dir / ".gitignore") "/.lake/\n/fva/.lake/\n"
  IO.FS.createDirAll (dir / o.lib)
  if let some w := o.wasm then
    let bs ← IO.FS.readBinFile w
    let file := (w : System.FilePath).fileName.getD "artifact.wasm"
    let rel := s!"{o.lib}/{file}"
    match FVA.Wasm.Decode.decode (FVA.Tool.packBytes bs) bs.size with
    | .ok m =>
      IO.FS.writeBinFile (dir / rel) bs
      IO.FS.writeFile (dir / o.lib / "Lifted.lean") (FVA.Tool.Lift.file s!"{o.lib}.Lifted" bs m rel)
    | .error e =>
      IO.eprintln s!"fva init: {w} does not decode: {repr e}"
      return 2
  IO.FS.writeFile (dir / o.lib / "Spec.lean") (specFile o.lib o.wasm.isSome)
  IO.FS.writeFile (dir / o.lib / "Proof.lean") (proofFile o.lib)
  IO.FS.writeFile (dir / s!"{o.lib}.lean") s!"import {o.lib}.Proof\n"
  IO.println (s!"Project written to {dir}. Next: cd {dir} && lake exe cache get && lake build, " ++
    s!"then write claims in {o.lib}/Spec.lean and check them with " ++
    s!"lake exe fva trust . --spec-module {o.lib}.Spec")
  return 0

end FVA.Tool.Init
