import FVA.Cli
import FVA.Tool.Decode
import FVA.Tool.Lift
import FVA.Tool.Difftest
import FVA.Tool.Trust
import FVA.Tool.Explain
import FVA.Tool.Certify
import FVA.Tool.Init

/-- CLI entry point. -/
def main (args : List String) : IO UInt32 := do
  if let cmd :: rest := args then
    if (rest.contains "--help" || rest.contains "-h") && (FVA.Cli.usage cmd).isSome then
      IO.print (FVA.Cli.usage cmd).get!
      return 0
  match args with
  | ["decode", path] =>
    IO.println (FVA.Tool.decodeSummary (← IO.FS.readBinFile path))
    return 0
  | "decode" :: paths@(_ :: _ :: _) =>
    for path in paths do
      IO.println s!"{path}: {FVA.Tool.decodeSummary (← IO.FS.readBinFile path)}"
    return 0
  | ["lift", path, out, "--ns", ns] =>
    -- `fva trust` reads the artifact back through this path, relative to the project root
    let rel : System.FilePath := path
    if rel.isAbsolute || rel.components.contains ".." then
      IO.eprintln "fva lift: give the .wasm path relative to the project root, without `..`"
      return 2
    let bs ← IO.FS.readBinFile path
    match FVA.Wasm.Decode.decode (FVA.Tool.packBytes bs) bs.size with
    | .ok m =>
      IO.FS.writeFile out (FVA.Tool.Lift.file ns bs m path)
      return 0
    | .error e =>
      IO.eprintln s!"fva lift: {repr e}"
      return 1
  | ["blob", path, out, "--ns", ns] =>
    let rel : System.FilePath := path
    if rel.isAbsolute || rel.components.contains ".." then
      IO.eprintln "fva blob: give the file's path relative to the project root, without `..`"
      return 2
    IO.FS.writeFile out (FVA.Tool.Blob.file ns (← IO.FS.readBinFile path) path)
    return 0
  | "certify" :: rest => FVA.Tool.Certify.main rest
  | "init" :: rest => do FVA.Tool.Init.main (← FVA.Tool.Trust.fvaRoot) rest
  | "difftest" :: rest => FVA.Tool.Difftest.main rest
  | "trust" :: rest => FVA.Tool.Trust.main rest
  | "trust-run" :: rest => FVA.Tool.Trust.run rest
  | "trust-matrix" :: rest => FVA.Tool.Trust.matrix rest
  | "explain" :: rest => FVA.Tool.Explain.main rest
  | _ =>
    let o := FVA.Cli.dispatch args
    IO.print o.out
    IO.eprint o.err
    return o.code
