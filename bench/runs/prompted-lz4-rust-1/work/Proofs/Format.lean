import Init

/- Independent block-format specification. Nat lengths cannot overflow.
   `strict = false` omits only end-of-block restrictions. -/
namespace Format

def extension : Nat → List Nat → Option (Nat × List Nat)
  | 0, _ => none
  | _ + 1, [] => none
  | k + 1, b :: bs =>
    if b == 255 then do
      let (n, rest) ← extension k bs
      pure (255+n, rest)
    else pure (b, bs)

def lengthField (base : Nat) (bs : List Nat) : Option (Nat × List Nat) :=
  if base < 15 then some (base, bs) else do
    let (n, rest) ← extension (bs.length+1) bs
    pure (15+n, rest)

def copyMatch : Nat → Nat → List Nat → Option (List Nat)
  | 0, _, out => some out
  | k + 1, offset, out => do
    if offset == 0 || offset > out.length then none else
      let b ← out[out.length-offset]?
      copyMatch k offset (out ++ [b])

def sequences (strict : Bool) : Nat → List Nat → List Nat → Option Nat → Option (List Nat)
  | 0, _, _, _ => none
  | _ + 1, [], _, _ => none
  | k + 1, token :: bs, out, lastMatch => do
    let (litLen, rest) ← lengthField (token/16) bs
    if litLen > rest.length then none else
    let out := out ++ rest.take litLen
    let rest := rest.drop litLen
    if rest.isEmpty then
      let endOK := (lastMatch.isNone || litLen ≥ 5) &&
        (match lastMatch with | none => true | some start => start+12 ≤ out.length)
      if !strict || endOK then some out else none
    else
      let lo :: hi :: rest := rest | none
      let offset := lo + 256*hi
      let (ml, rest) ← lengthField (token%16) rest
      let start := out.length
      let out ← copyMatch (ml+4) offset out
      if rest.isEmpty && !strict then some out
      else sequences strict k rest out (some start)

def decode (strict : Bool) (input : List Nat) : Option (List Nat) :=
  if input.all (· < 256) then sequences strict (input.length+1) input [] none else none

end Format
