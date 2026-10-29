/- Independent reading of lz4_Block_format.md. Natural numbers denote bytes.
   Arithmetic here is unbounded. No code from the Rust decoder is translated here. -/
namespace LZ4

def extra : Nat → Nat → List Nat → Option (Nat × List Nat)
  | 0, _, _ => none
  | _+1, _, [] => none
  | f+1, total, b::bs =>
    if b == 255 then extra f (total+b) bs else some (total+b, bs)

def lengthField (nibble : Nat) (input : List Nat) : Option (Nat × List Nat) :=
  if nibble == 15 then extra (input.length+1) 15 input else some (nibble, input)

def matchCopy : Nat → Nat → List Nat → Option (List Nat)
  | 0, _, out => some out
  | f+1, offset, out => do
    if offset == 0 || offset > out.length then none else
      let b ← out[out.length-offset]?
      matchCopy f offset (out ++ [b])

structure Decoded where
  output : List Nat
  matchStarts : List Nat
  finalLiterals : Nat
  endsInLiterals : Bool
  deriving DecidableEq, Repr

def sequences : Nat → List Nat → List Nat → List Nat → Option Decoded
  | 0, _, _, _ => none
  | _+1, [], _, _ => none
  | f+1, token::input, out, starts => do
    let (ll, input) ← lengthField (token/16) input
    if ll > input.length then none else
      let out := out ++ input.take ll
      let rest := input.drop ll
      if rest.isEmpty then pure ⟨out, starts, ll, true⟩ else
        let lo :: hi :: rest := rest | none
        let offset := lo + 256*hi
        if offset == 0 || offset > out.length then none else
          let (ml, rest) ← lengthField (token%16) rest
          let output ← matchCopy (ml+4) offset out
          let starts := starts ++ [out.length]
          if rest.isEmpty then pure ⟨output, starts, 0, false⟩
          else sequences f rest output starts

def decode (input : List Nat) : Option Decoded :=
  if input.all (· < 256) then sequences (input.length+1) input [] [] else none

-- With no matches the sole final sequence contains all the original literals.
-- With matches, require final literals >= 5 and every match to start >= 12 bytes
-- before the end of decoded content (equivalent to checking the last match).
def endConditions (d : Decoded) : Bool :=
  d.endsInLiterals && (d.matchStarts.isEmpty ||
    (d.finalLiterals ≥ 5 && d.matchStarts.all (fun p => p+12 ≤ d.output.length)))

end LZ4
