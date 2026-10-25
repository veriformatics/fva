import Init

namespace LZ4

-- Specification only: lists contain natural-number byte values.
-- Read the mandatory extension byte(s) when a token nibble equals 15.
def extension (n : Nat) : List Nat → Option (Nat × List Nat)
  | [] => none
  | b :: bs => if b = 255 then extension (n + b) bs else some (n + b, bs)

def lengthField (n : Nat) (bs : List Nat) : Option (Nat × List Nat) :=
  if n < 15 then some (n, bs) else extension n bs

-- Byte-at-a-time copying permits an overlapping match (e.g. offset 1).
def matchCopy : Nat → Nat → List Nat → List Nat
  | 0, _, out => out
  | n + 1, offset, out => matchCopy n offset (out ++ [out[out.length - offset]!])

-- Parse sequences. lastStart records the most recent match's output position.
-- Fuel bounds the number of tokens, not literal or match lengths.
def sequences : Nat → List Nat → List Nat → Option Nat → Option (List Nat)
  | 0, _, _, _ => none
  | fuel + 1, bs, out, lastStart => do
      let token :: rest := bs | none
      let (llen, rest) ← lengthField (token / 16) rest
      if rest.length < llen then none else do
        let literals := rest.take llen
        let rest := rest.drop llen
        let out := out ++ literals
        if rest.isEmpty then
          match lastStart with
          | none => some out
          | some start =>
              if 5 ≤ llen ∧ start + 12 ≤ out.length then some out else none
        else do
          let lo :: hi :: rest := rest | none
          let offset := lo + 256 * hi
          if offset = 0 ∨ out.length < offset then none else do
            let (mlen, rest) ← lengthField (token % 16) rest
            sequences fuel rest (matchCopy (mlen + 4) offset out) (some out.length)

def decode (bs : List Nat) : Option (List Nat) :=
  if bs.all (· < 256) then sequences bs.length bs [] none else none

def valid (bs : List Nat) : Prop := (decode bs).isSome = true

-- Exact vectors also asserted by both runtime harnesses.
def encoderInput : List Nat := [97,98,99,100,101,102,97,98,99,100,120,121,122]
def encoderBlock : List Nat := [96,97,98,99,100,101,102,6,0,48,120,121,122]
def goodBlock : List Nat := [19,97,1,0,80,97,97,97,97,97]

theorem r1_invalid : ¬ valid encoderBlock := by
  unfold valid
  decide

theorem r2_content : decode goodBlock = some (List.replicate 13 97) := by decide

theorem r2_valid : valid goodBlock := by
  unfold valid
  decide

theorem r2_wrong_length : (1 : Nat) ≠ (List.replicate 13 97).length := by decide

theorem r3_empty_valid : decode [0] = some [] ∧ valid [0] := by
  unfold valid
  decide

theorem r3_outside : ¬ (65535 ≤ (65536 : Nat) ∧ 65536 < 65535 + 1) := by decide

-- An axiom-free canary used to feed ill-typed proof terms to independent kernels.
theorem kernelCanary : (0 : Nat) = 0 := rfl

end LZ4
