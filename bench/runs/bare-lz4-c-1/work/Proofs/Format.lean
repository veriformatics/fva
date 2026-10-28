import Proofs.Wasm

/- A small independent specification of the supplied block-format document.
   Offsets of zero are enabled only in the relaxed (R3) interpretation. -/
namespace LZ4Format

def extension : Nat → List Nat → Option (Nat × List Nat)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, x :: xs =>
    if x > 255 then none
    else if x = 255 then do
      let (n, tail) ← extension fuel xs
      pure (x + n, tail)
    else some (x, xs)

def lengthField (n : Nat) (xs : List Nat) : Option (Nat × List Nat) :=
  if n = 15 then do
    let (extra, tail) ← extension xs.length xs
    pure (15 + extra, tail)
  else some (n, xs)

def copyMatch (offset : Nat) : Nat → List Nat → List Nat
  | 0, out => out
  | n + 1, out => copyMatch offset n
      (out ++ [if offset = 0 then 0 else out[out.length - offset]!])

structure Decoded where
  bytes : List Nat
  lastMatch : Option Nat
  lastLiterals : Nat
  deriving DecidableEq, Repr

def sequences (zeroOffset : Bool) : Nat → List Nat → List Nat → Option Nat → Option Decoded
  | 0, _, _, _ => none
  | _ + 1, [], _, _ => none
  | fuel + 1, token :: input, out, last => do
    if token > 255 then none else do
      let (ll, input) ← lengthField (token / 16) input
      if ll > input.length then none else do
        let literals := input.take ll
        if !(literals.all (· < 256)) then none else do
          let out := out ++ literals
          let input := input.drop ll
          if input.isEmpty then some ⟨out, last, ll⟩ else do
            let low :: high :: input := input | none
            if low > 255 ∨ high > 255 then none else do
              let offset := low + 256 * high
              if offset > out.length ∨ (offset = 0 ∧ !zeroOffset) then none else do
                let (ml, input) ← lengthField (token % 16) input
                sequences zeroOffset fuel input (copyMatch offset (ml + 4) out) (some out.length)

def decode (zeroOffset : Bool) (input : List Nat) : Option Decoded :=
  sequences zeroOffset input.length input [] none

def endOK (d : Decoded) : Bool :=
  match d.lastMatch with
  | none => true
  | some start => d.lastLiterals ≥ 5 && start + 12 ≤ d.bytes.length

def validIndependent (input output : List Nat) : Prop :=
  ∃ d, decode false input = some d ∧ d.bytes = output ∧ endOK d = true

def relaxedDecodes (input output : List Nat) : Prop :=
  ∃ d, decode true input = some d ∧ d.bytes = output

end LZ4Format
