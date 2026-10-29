import Init

/- Independent, executable reading of lz4_Block_format.md. Fuel counts
   sequences, not bytes. The public entry supplies more fuel than there can
   be sequences. This is a specification, not a model of the Rust decoder. -/
namespace LZ4
structure Decoded where
  content : List Nat
  finalLiterals : Nat
  lastMatchStart : Option Nat
  deriving DecidableEq, Repr

def extra : List Nat → Option (Nat × List Nat)
  | [] => none
  | b :: bs => if b = 255 then do
      let (v, rest) ← extra bs
      pure (255 + v, rest)
    else if b < 255 then some (b, bs) else none

def lengthField (nibble : Nat) (bs : List Nat) : Option (Nat × List Nat) :=
  if nibble < 15 then some (nibble, bs) else do
    let (v, rest) ← extra bs
    pure (15 + v, rest)

def matchCopy (offset : Nat) : Nat → List Nat → Option (List Nat)
  | 0, out => some out
  | n+1, out => do
    if offset = 0 ∨ out.length < offset then none else do
      let b ← out[out.length-offset]?
      matchCopy offset n (out ++ [b])

def sequences : Nat → List Nat → List Nat → Option Nat → Option Decoded
  | 0, _, _, _ => none
  | _+1, [], _, _ => none
  | fuel+1, token :: bs, out, last => do
    let (litLen, bs) ← lengthField (token / 16) bs
    if litLen > bs.length then none else do
      let out := out ++ bs.take litLen
      let bs := bs.drop litLen
      if bs.isEmpty then some ⟨out, litLen, last⟩ else do
        match bs with
        | lo :: hi :: bs => do
          let offset := lo + 256 * hi
          let (matchLen, bs) ← lengthField (token % 16) bs
          let copied ← matchCopy offset (matchLen + 4) out
          sequences fuel bs copied (some out.length)
        | _ => none

def decode (bs : List Nat) : Option Decoded :=
  if bs.all (· < 256) then sequences (bs.length+1) bs [] none else none

def validIndependent (bs out : List Nat) : Bool :=
  match decode bs with
  | none => false
  | some d => d.content == out && match d.lastMatchStart with
      | none => true
      | some pos => d.finalLiterals ≥ 5 && pos + 12 ≤ d.content.length

/-- R3's content/sequence condition, allowing relaxed end conditions. -/
def relaxedDecode (bs out : List Nat) : Bool :=
  match decode bs with
  | none => false
  | some d => d.content == out
end LZ4
