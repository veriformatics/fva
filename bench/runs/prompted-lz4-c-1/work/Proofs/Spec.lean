/- Executable independent-block format specification, including the two R3 relaxations. -/
namespace LZ4
structure Decoded where
  content : List Nat
  conforming : Bool
  deriving Repr, DecidableEq

def lengthField (base : Nat) (bs : List Nat) : Option (Nat × List Nat) :=
  if base < 15 then some (base,bs) else go bs.length bs 15
where
  go : Nat → List Nat → Nat → Option (Nat × List Nat)
    | 0, _, _ => none
    | _+1, [], _ => none
    | fuel+1, b::bs, n => if b == 255 then go fuel bs (n+b) else some (n+b,bs)

def copyMatch (out : List Nat) (offset length : Nat) : Option (List Nat) :=
  if offset == 0 then some (out ++ List.replicate length 0)
  else if offset > out.length then none
  else (List.range length).foldlM (fun acc _ => do
    let b ← acc[acc.length-offset]?
    pure (acc ++ [b])) out

def sequences : Nat → List Nat → List Nat → Bool → Option Nat → Option Decoded
  | 0, _, _, _, _ => none
  | _+1, [], _, _, _ => none
  | fuel+1, token::bs, out, offsetsValid, lastMatch => do
    let (lit, bs) ← lengthField (token/16) bs
    if lit > bs.length then none else do
      let out := out ++ bs.take lit
      let bs := bs.drop lit
      if bs.isEmpty then
        pure ⟨out, offsetsValid && (match lastMatch with
          | none => true
          | some start => lit ≥ 5 && start+12 ≤ out.length)⟩
      else do
        let lo::hi::bs := bs | none
        let offset := lo + 256*hi
        let (ml, bs) ← lengthField (token%16) bs
        let next ← copyMatch out offset (ml+4)
        sequences fuel bs next (offsetsValid && offset != 0) (some out.length)

def decode (bs : List Nat) : Option Decoded :=
  if bs.all (· < 256) then sequences bs.length bs [] true none else none
end LZ4
