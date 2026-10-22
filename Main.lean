import FVA
import FVA.Tool.Decode

/-- CLI entry point. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["decode", path] =>
    IO.println (FVA.Tool.decodeSummary (← IO.FS.readBinFile path))
    return 0
  | _ =>
    let o := FVA.Cli.dispatch args
    IO.print o.out
    IO.eprint o.err
    return o.code
