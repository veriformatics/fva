import Proofs.Cases
import Lean
open Lean Verification

def caseJSON (c : Case) : Json := Json.mkObj [
  ("input", toJson c.input), ("cap", toJson c.cap), ("expected", toJson c.expected),
  ("src", toJson c.src), ("dst", toJson c.dst), ("fill", toJson c.fill),
  ("output", toJson ((LZ4.decode c.input).map LZ4.Decoded.content)),
  ("valid", toJson (((LZ4.decode c.input).map LZ4.Decoded.conforming).getD false))]

def main : IO Unit := IO.println (toJson (cases.map caseJSON)).compress
