import Init
/- Executable reading of the block grammar. No dictionary; offset zero is invalid.
   End conditions are checked separately so R3 permits their relaxation. -/
namespace Format
structure Parsed where
  content : List Nat
  lastLiterals : Nat
  lastMatch : Option Nat
  deriving BEq

def extension : List Nat → Option (Nat × List Nat)
  | [] => none
  | b :: bs => if b = 255 then do
      let (n, rest) ← extension bs
      some (255+n, rest)
    else some (b, bs)
def lengthField (n : Nat) (input : List Nat) : Option (Nat × List Nat) :=
  if n = 15 then do
    let (extra, rest) ← extension input
    some (15+extra, rest)
  else some (n, input)
def matchCopy (offset : Nat) : Nat → List Nat → List Nat
  | 0, out => out
  | n+1, out => matchCopy offset n (out ++ [out[out.length-offset]?.getD 0])
def sequences : Nat → List Nat → List Nat → Option Nat → Option Parsed
  | 0, _, _, _ => none
  | fuel+1, input, out, lastMatch => do
    let token :: rest := input | none
    let (litlen, rest) ← lengthField (token / 16) rest
    if rest.length < litlen then none else do
      let out := out ++ rest.take litlen
      let rest := rest.drop litlen
      if rest.isEmpty then some ⟨out, litlen, lastMatch⟩ else do
        let lo :: hi :: rest := rest | none
        let offset := lo + 256*hi
        if offset = 0 ∨ out.length < offset then none else do
          let (len, rest) ← lengthField (token % 16) rest
          sequences fuel rest (matchCopy offset (len+4) out) (some out.length)
def parse (input : List Nat) : Option Parsed :=
  if input.all (· < 256) then sequences (input.length+1) input [] none else none
def endConditions (p : Parsed) : Bool :=
  match p.lastMatch with
  | none => true
  | some pos => p.lastLiterals ≥ 5 && pos+12 ≤ p.content.length
end Format
