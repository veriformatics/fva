import Proofs.Results
import Lean.Data.Json
open Lean Results

def main : IO Unit := do
  let cases := Results.cases.map fun c =>
    Json.mkObj [("input", toJson c.input), ("cap", toJson c.cap),
      ("result", toJson c.result), ("output", toJson c.output), ("valid", toJson c.valid)]
  IO.println (toJson cases).compress
