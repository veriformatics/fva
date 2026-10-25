import Mathlib

/- A reference interpretation of the supplied LZ4 block format, independent of
   the implementation. Bytes and lengths are mathematical natural numbers.
   Fuel bounds parsing by the number of input bytes, not decoded bytes. -/
namespace LZ4

def readExtension : Nat → Nat → List Nat → Option (Nat × List Nat)
  | 0, _, _ => none
  | fuel + 1, n, b :: bs =>
      if b = 255 then readExtension fuel (n + b) bs else some (n + b, bs)
  | _ + 1, _, [] => none

-- Append one byte at a time: matches may overlap their own generated output.
def copyMatch : Nat → Nat → List Nat → Option (List Nat)
  | 0, _, out => some out
  | n + 1, offset, out => do
      if offset = 0 ∨ out.length < offset then none else do
        let b ← out[out.length - offset]?
        copyMatch n offset (out ++ [b])

def endConditions (literalLength : Nat) (out : List Nat)
    (lastMatchStart : Option Nat) : Bool :=
  match lastMatchStart with
  | none => true
  | some start => decide (5 ≤ literalLength ∧ start + 12 ≤ out.length)

def parseSequences : Nat → Bool → List Nat → List Nat → Option Nat →
    Option (List Nat)
  | 0, _, _, _, _ => none
  | fuel + 1, enforceEnd, token :: rest, out, lastStart => do
      let (literalLength, rest) ←
        if token / 16 = 15 then readExtension (rest.length + 1) 15 rest
        else some (token / 16, rest)
      if rest.length < literalLength then none else do
        let out := out ++ rest.take literalLength
        let rest := rest.drop literalLength
        if rest.isEmpty then
          if !enforceEnd || endConditions literalLength out lastStart
          then some out else none
        else
          match rest with
          | lo :: hi :: rest => do
              let offset := lo + 256 * hi
              if offset = 0 ∨ out.length < offset then none else do
                let (matchLength, rest) ←
                  if token % 16 = 15 then readExtension (rest.length + 1) 19 rest
                  else some (token % 16 + 4, rest)
                let next ← copyMatch matchLength offset out
                parseSequences fuel enforceEnd rest next (some out.length)
          | _ => none
  | _ + 1, _, [], _, _ => none

def decodeWith (enforceEnd : Bool) (block : List Nat) : Option (List Nat) :=
  if block.all (fun b => b < 256) then
    parseSequences (block.length + 1) enforceEnd block [] none
  else none

def decode := decodeWith true
def decodeIgnoringEndConditions := decodeWith false

-- ASCII "abcdabcd12345".
def r1Input : List Nat := [97, 98, 99, 100, 97, 98, 99, 100, 49, 50, 51, 52, 53]
-- Token 0x40, four literals, offset 4, match length 4, five final literals.
def r1Wire : List Nat := [64, 97, 98, 99, 100, 4, 0, 80, 49, 50, 51, 52, 53]

theorem r1_rejected : decode r1Wire = none := by decide
theorem r1_content : decodeIgnoringEndConditions r1Wire = some r1Input := by decide
theorem r1_last_match_too_late : ¬ (4 + 12 ≤ r1Input.length) := by decide

-- One literal 'a', offset 1 and length 7, then five final 'a' literals.
def r2Wire : List Nat := [19, 97, 1, 0, 80, 97, 97, 97, 97, 97]
def r2Content : List Nat := List.replicate 13 97

theorem r2_valid_content : decode r2Wire = some r2Content := by decide
theorem r2_length : r2Content.length = 13 := by decide
theorem r2_wrong_return : (1 : Nat) ≠ r2Content.length := by decide

theorem empty_valid_content : decode [0] = some [] := by decide
theorem boundary_address_outside :
    ¬ (65535 ≤ (65536 : Nat) ∧ 65536 < 65535 + 1) := by decide

end LZ4
