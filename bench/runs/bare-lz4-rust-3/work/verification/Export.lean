import Proofs.Fixtures
open Verification Lean

def nums (xs : List Nat) : Json := toJson xs

def exportCase (c : Case) : Json := Id.run do
  let s := caseState c
  let fields := [
    ("input", nums c.input), ("src", toJson c.src), ("dst", toJson c.dst),
    ("cap", toJson c.cap), ("expected", toJson c.expected),
    ("modelResult", toJson s.result),
    ("modelOutput", nums ((List.range c.cap).map (fun i => byteAt (initialMemory c) s (c.dst+i))))]
  return Json.mkObj fields

#eval do
  let cases := corpus ++ tokenCases
  unless cases.all checkCase do throw (IO.userError "model case check failed")
  unless cases.all referenceAgrees do throw (IO.userError "reference check failed")
  unless validCases.all validReference do throw (IO.userError "valid-format check failed")
  IO.println "PASS: executable model checks of all 570 cases and 35 valid blocks"
  IO.FS.writeFile "verification/cases.json" ((toJson (cases.map exportCase)).compress ++ "\n")
  IO.println s!"Exported {cases.length} cases from the Lean model"
