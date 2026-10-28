import Proofs.Wasm

/- Independent executable reading of lz4_Block_format.md. Parsing is exact:
   no leftover compressed bytes, offsets cannot exceed decoded length.
   End conditions are checked separately, to express R3's relaxation.
   The offset-zero relaxation is explicit, never normal LZ4 validity. -/
namespace Verification

def lengthField : Nat → List Nat → Option (Nat × List Nat)
  | 0, _ => none
  | fuel + 1, b :: rest =>
    if b = 255 then do
      let (n, tail) ← lengthField fuel rest
      pure (255 + n, tail)
    else if b < 255 then some (b, rest) else none
  | _ + 1, [] => none

def field (n : Nat) (xs : List Nat) : Option (Nat × List Nat) :=
  if n = 15 then do
    let (extra, rest) ← lengthField (xs.length + 1) xs
    pure (15 + extra, rest)
  else some (n, xs)

def matchBytes : Nat → Nat → List Nat → Option (List Nat)
  | 0, _, output => some output
  | n + 1, offset, output => do
    let b ← output[output.length - offset]?
    matchBytes n offset (output ++ [b])

structure Decoded where
  bytes : List Nat
  starts : List Nat
  finalLiterals : Nat
  zeroOffset : Bool
  deriving DecidableEq, Repr

def parseSequences (allowZero : Bool) : Nat → List Nat → List Nat → List Nat → Bool → Option Decoded
  | 0, _, _, _, _ => none
  | fuel + 1, token :: rest, output, starts, zero => do
    if token ≥ 256 then none else do
      let (ll, rest) ← field (token / 16) rest
      if rest.length < ll then none else do
        let output := output ++ rest.take ll
        let rest := rest.drop ll
        if rest.isEmpty then
          some ⟨output, starts, ll, zero⟩
        else match rest with
        | lo :: hi :: rest => do
          if lo ≥ 256 ∨ hi ≥ 256 then none else do
            let offset := lo + hi * 256
            if offset > output.length ∨ (offset = 0 ∧ !allowZero) then none else do
              let (ml, rest) ← field (token % 16) rest
              let start := output.length
              let output ← if offset = 0 then some (output ++ List.replicate (ml + 4) 0)
                else matchBytes (ml + 4) offset output
              parseSequences allowZero fuel rest output (starts ++ [start]) (zero || offset == 0)
        | _ => none
  | _ + 1, [], _, _, _ => none

def parseBlock (allowZero : Bool) (input : List Nat) : Option Decoded :=
  if input.all (· < 256) then
    parseSequences allowZero (input.length + 1) input [] [] false
  else none

def endConditions (d : Decoded) : Bool :=
  if d.starts.isEmpty then true
  else d.finalLiterals ≥ 5 && d.starts.all (fun p => p + 12 ≤ d.bytes.length)

def validIndependent (input : List Nat) : Bool :=
  match parseBlock false input with
  | some d => endConditions d
  | none => false

end Verification
