import Proofs.Claims
import Lean
open Lean Verification

def main : IO Unit := do
  let entries := cases.map fun c => Json.mkObj [
    ("input",toJson c.input),("cap",toJson c.cap),
    ("src",toJson c.src),("dst",toJson c.dst),
    ("expected",match c.expected with | none => Json.null | some bs => toJson bs)]
  IO.println (Json.compress (toJson entries))
