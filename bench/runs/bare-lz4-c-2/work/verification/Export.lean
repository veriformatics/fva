import Proofs.Cases
import Lean

open Verification Verification.Cases Lean

def pairJson (p : Nat × Nat) : Json := toJson [p.1, p.2]

def caseJson (c : Case) : IO Json := do
  let some r := execute c | throw (IO.userError s!"execution failed: {c.name}")
  unless check c do throw (IO.userError s!"check failed: {c.name}")
  return Json.mkObj [
    ("name", toJson c.name), ("src", toJson c.src), ("dst", toJson c.dst),
    ("input", toJson c.input), ("capacity", toJson c.capacity),
    ("return", toJson r.value), ("initial", toJson ((initialMemory c).map pairJson)),
    ("final", toJson (r.mem.map pairJson)),
    ("accesses", toJson r.accesses.length)]

def main : IO Unit := do
  let results ← cases.mapM caseJson
  IO.println (toJson results).compress
