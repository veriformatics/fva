import FVA
import FVA.Tool.Decode
import FVA.Tool.Lift

/-- CLI entry point. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["decode", path] =>
    IO.println (FVA.Tool.decodeSummary (← IO.FS.readBinFile path))
    return 0
  | ["lift", path, out, "--ns", ns] =>
    let bs ← IO.FS.readBinFile path
    let packed := FVA.Tool.packBytes bs
    match FVA.Wasm.Decode.decode packed bs.size with
    | .ok m =>
      IO.FS.writeFile out (FVA.Tool.Lift.file ns packed bs.size m)
      return 0
    | .error e =>
      IO.eprintln s!"fva lift: {repr e}"
      return 1
  | _ =>
    let o := FVA.Cli.dispatch args
    IO.print o.out
    IO.eprint o.err
    return o.code
