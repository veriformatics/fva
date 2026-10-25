import Proofs.Counterexamples

-- Keep the executable artifact checks bound to the exact Lean witnesses.
def jsonArray (xs : List Nat) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

def main : IO Unit := IO.println <|
  "{\"encoderInput\":" ++ jsonArray LZ4.encoderInput ++
  ",\"encoderBlock\":" ++ jsonArray LZ4.encoderBlock ++
  ",\"decoderBlock\":" ++ jsonArray LZ4.decoderBlock ++
  ",\"decoderContent\":" ++ jsonArray LZ4.decoderContent ++
  ",\"emptyBlock\":" ++ jsonArray LZ4.emptyBlock ++ "}"
