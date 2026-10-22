import FVA.Cli
import FVA.Tool.Decode
import FVA.Tool.Lift
import FVA.Tool.Difftest

/-- CLI entry point. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["decode", path] =>
    IO.println (FVA.Tool.decodeSummary (← IO.FS.readBinFile path))
    return 0
  | "decode" :: paths@(_ :: _ :: _) =>
    for path in paths do
      IO.println s!"{path}: {FVA.Tool.decodeSummary (← IO.FS.readBinFile path)}"
    return 0
  | ["lift", path, out, "--ns", ns] =>
    let bs ← IO.FS.readBinFile path
    match FVA.Wasm.Decode.decode (FVA.Tool.packBytes bs) bs.size with
    | .ok m =>
      IO.FS.writeFile out (FVA.Tool.Lift.file ns bs m)
      return 0
    | .error e =>
      IO.eprintln s!"fva lift: {repr e}"
      return 1
  | "difftest" :: rest => FVA.Tool.Difftest.main rest
  | _ =>
    let o := FVA.Cli.dispatch args
    IO.print o.out
    IO.eprint o.err
    return o.code
