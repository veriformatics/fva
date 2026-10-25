import Proofs

open Verification

def main : IO Unit :=
  IO.println ("{\"encoderInput\":" ++ reprStr encoderInput ++
    ",\"encoderBlock\":" ++ reprStr encoderBlock ++
    ",\"validBlock\":" ++ reprStr validBlock ++
    ",\"validContent\":" ++ reprStr validContent ++
    ",\"emptyBlock\":" ++ reprStr emptyBlock ++ "}")
