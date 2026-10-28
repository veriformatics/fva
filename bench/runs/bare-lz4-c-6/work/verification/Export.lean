import Proofs.Cases
import Lean

open Cases LZ4Spec Lean

def caseJSON (c : Case) : Json :=
  Json.mkObj [
    ("name", toJson c.name), ("input", toJson c.input),
    ("src", toJson c.src), ("dst", toJson c.dst),
    ("capacity", toJson c.capacity), ("expected", toJson c.expected),
    ("output", toJson (((decode c.input).map (·.bytes)).getD []))]

def main (args : List String) : IO Unit := do
  let content := (toJson (examples.map caseJSON)).compress ++ "\n"
  if args == ["--check"] then
    unless (← IO.FS.readFile "verification/cases.json") == content do
      throw (IO.userError "cases.json differs from Lean case definitions")
    IO.println "PASS: runtime cases agree with Lean definitions"
  else
    IO.FS.writeFile "verification/cases.json" content
