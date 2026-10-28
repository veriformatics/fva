import Proofs.Results
import Lean
open Lean

def main : IO Unit := do
  let cases := Results.cases.map fun c => Json.mkObj [
    ("name", toJson c.name), ("input", toJson c.input),
    ("capacity", toJson c.capacity), ("result", toJson c.result),
    ("output", toJson c.output), ("src", toJson c.src), ("dst", toJson c.dst)]
  IO.println (toJson cases).compress
