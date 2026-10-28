import Mathlib.Data.List.Basic

/- Executable reading of lz4_Block_format.md. This is a specification, not a
   translation of the C decoder: no wild copies or parsing safety margins. -/
namespace Verification.Format

def extension : List Nat → Option (Nat × List Nat)
  | [] => none
  | b :: bs => if b = 255 then do
      let (n, rest) ← extension bs
      return (255 + n, rest)
    else some (b, bs)

def lengthField (n : Nat) (bs : List Nat) : Option (Nat × List Nat) :=
  if n = 15 then do
    let (extra, rest) ← extension bs
    return (15 + extra, rest)
  else some (n, bs)

-- Increasing output one byte at a time implements overlapping matches.
def copyMatch (offset : Nat) : Nat → List Nat → Option (List Nat)
  | 0, out => some out
  | n + 1, out => do
    let b ← if offset = 0 then some 0 else out[out.length - offset]?
    copyMatch offset n (out ++ [b])

structure Decoded where
  content : List Nat
  matchStarts : List Nat
  finalLiterals : Nat
  deriving Repr, DecidableEq

def sequences (zeroAllowed : Bool) : Nat → List Nat → List Nat → List Nat → Option Decoded
  | 0, _, _, _ => none
  | fuel + 1, input, out, starts => do
    let token ← input.head?
    let (ll, rest) ← lengthField (token / 16) (input.drop 1)
    if ll > rest.length then none else do
      let out := out ++ rest.take ll
      let rest := rest.drop ll
      if rest.isEmpty then return ⟨out, starts, ll⟩ else do
        match rest with
        | lo :: hi :: rest =>
          let offset := lo + 256 * hi
          if (offset = 0 ∧ !zeroAllowed) ∨ offset > out.length then none else do
            let (ml, rest) ← lengthField (token % 16) rest
            let content ← copyMatch offset (ml + 4) out
            sequences zeroAllowed fuel rest content (starts ++ [out.length])
        | _ => none

def decode (zeroAllowed : Bool) (input : List Nat) : Option Decoded :=
  if input.all (· < 256) then sequences zeroAllowed input.length input [] [] else none

def endConditions (d : Decoded) : Bool :=
  (d.matchStarts.isEmpty || d.finalLiterals ≥ 5) &&
    d.matchStarts.all (fun start => start + 12 ≤ d.content.length)

def validIndependent (input content : List Nat) : Bool :=
  match decode false input with
  | none => false
  | some d => d.content == content && endConditions d

end Verification.Format
