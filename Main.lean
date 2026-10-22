import FVA

/-- CLI entry point. -/
def main (args : List String) : IO UInt32 := do
  let o := FVA.Cli.dispatch args
  IO.print o.out
  IO.eprint o.err
  return o.code
