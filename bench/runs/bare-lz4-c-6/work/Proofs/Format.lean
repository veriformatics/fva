import Proofs.Wasm

/- A separate, total specification of LZ4 parsing and sequential match copying.
   This is not the implementation, and no general equivalence is asserted. -/
namespace LZ4Spec

structure Decoded where
  bytes : List Nat
  lastLiterals : Nat
  lastMatchStart : Option Nat
  zeroOffset : Bool
  deriving Repr, DecidableEq

-- An extension must end in a byte other than 255. Fuel bounds parsing work.
def extension : Nat → List Nat → Option (Nat × List Nat)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, b :: rest =>
    if b = 255 then do
      let (n, tail) ← extension fuel rest
      some (255 + n, tail)
    else some (b, rest)

def lengthField (fuel field : Nat) (input : List Nat) : Option (Nat × List Nat) :=
  if field = 15 then do
    let (n, rest) ← extension fuel input
    some (15 + n, rest)
  else some (field, input)

-- Sequential copying implements overlap. Offset zero has the R3 extension.
def matchCopy (offset : Nat) : Nat → List Nat → List Nat
  | 0, output => output
  | n + 1, output =>
    let byte := if offset = 0 then 0 else output[output.length - offset]!
    matchCopy offset n (output ++ [byte])

def parseLoop : Nat → List Nat → List Nat → Option Nat → Bool → Option Decoded
  | 0, _, _, _, _ => none
  | _ + 1, [], _, _, _ => none
  | fuel + 1, token :: input, output, lastMatch, zero => do
    let (ll, input) ← lengthField (fuel + 1) (token / 16) input
    if ll > input.length then none else
      let output := output ++ input.take ll
      let input := input.drop ll
      if input.isEmpty then
        some ⟨output, ll, lastMatch, zero⟩
      else do
        let lo :: hi :: input := input | none
        let offset := lo + 256 * hi
        if offset > output.length then none else
          let (ml, input) ← lengthField (fuel + 1) (token % 16) input
          let ml := ml + 4
          let pos := output.length
          parseLoop fuel input (matchCopy offset ml output) (some pos)
            (zero || offset == 0)

def decode (input : List Nat) : Option Decoded :=
  if input.all (· < 256) then parseLoop (input.length + 1) input [] none false
  else none

def endConditions (d : Decoded) : Bool :=
  match d.lastMatchStart with
  | none => true
  | some start => d.lastLiterals ≥ 5 && start + 12 ≤ d.bytes.length

def validIndependent (input : List Nat) : Bool :=
  match decode input with
  | none => false
  | some d => !d.zeroOffset && endConditions d

end LZ4Spec
