import Proofs.Wasm

/-! Independent, simple LZ4 sequence interpreter. Unbounded natural lengths,
byte-at-a-time overlapping copies; no optimization from lz4_flex is reused.
The last-match distance in `endConditions` is measured in decoded bytes.
This definition's correspondence with the English format is a review obligation.
-/
namespace Verification

def extraLength : Nat → List Nat → Option (Nat × List Nat)
  | 0, _ => none
  | _, [] => none
  | fuel + 1, b :: bs =>
    if b == 255 then do
      let (n, rest) ← extraLength fuel bs
      pure (255 + n, rest)
    else pure (b, bs)

def lengthField (n : Nat) (bs : List Nat) : Option (Nat × List Nat) :=
  if n == 15 then do
    let (extra, rest) ← extraLength (bs.length + 1) bs
    pure (15 + extra, rest)
  else pure (n, bs)

def matchCopy (out : List Nat) (offset len : Nat) : List Nat :=
  (List.range len).foldl (fun xs _ => xs ++ [xs[xs.length - offset]!]) out

structure Decoded where
  bytes : List Nat
  lastLiterals : Nat
  sequences : Nat
  matchStarts : List Nat
  deriving Repr, DecidableEq

def sequences : Nat → List Nat → List Nat → Nat → List Nat → Option Decoded
  | 0, _, _, _, _ => none
  | _, [], _, _, _ => none
  | fuel + 1, token :: bs, out, count, starts => do
    let (litLen, bs) ← lengthField (token / 16) bs
    if litLen > bs.length then none else do
      let out := out ++ bs.take litLen
      let rest := bs.drop litLen
      if rest.isEmpty then pure ⟨out, litLen, count + 1, starts⟩ else
        match rest with
        | lo :: hi :: rest =>
          let offset := lo + 256 * hi
          if offset == 0 || offset > out.length then none else do
            let (matchLen, rest) ← lengthField (token % 16) rest
            let bytes := matchCopy out offset (matchLen + 4)
            sequences fuel rest bytes (count + 1) (out.length :: starts)
        | _ => none

def reference (input : List Nat) : Option Decoded :=
  if input.all (· < 256) then sequences (input.length + 1) input [] 0 [] else none

def endConditions (d : Decoded) : Bool :=
  (d.lastLiterals ≥ 5 || (d.sequences == 1 && d.lastLiterals < 5)) &&
    d.matchStarts.all (fun pos => pos + 12 ≤ d.bytes.length)

end Verification
