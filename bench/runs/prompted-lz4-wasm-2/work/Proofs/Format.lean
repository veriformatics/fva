import Init

namespace Verification

-- Specification only: natural-number bytes, independent blocks, no dictionary.
-- Length extensions are terminated by a byte smaller than 255.
def extension : Nat → List Nat → Option (Nat × List Nat)
  | 0, _ => none
  | _ + 1, [] => none
  | k + 1, b :: bs =>
    if b = 255 then do
      let (n, rest) ← extension k bs
      pure (b + n, rest)
    else some (b, bs)

def fieldLength (base : Nat) (bs : List Nat) : Option (Nat × List Nat) :=
  if base = 15 then do
    let (n, rest) ← extension (bs.length + 1) bs
    pure (15 + n, rest)
  else some (base, bs)

-- Forward byte copying permits overlapping matches, as required by LZ4.
def matchCopy : Nat → Nat → List Nat → List Nat
  | 0, _, out => out
  | n + 1, offset, out =>
    matchCopy n offset (out ++ [out[out.length - offset]!])

-- Fuel bounds the number of sequences, each of which consumes a token.
-- lastStart records the decoded position of the most recent match.
def sequences : Nat → List Nat → List Nat → Option Nat → Option (List Nat)
  | 0, _, _, _ => none
  | _ + 1, [], _, _ => none
  | k + 1, token :: bs, out, lastStart => do
    let (llen, afterLength) ← fieldLength (token / 16) bs
    if llen > afterLength.length then none else do
      let nextOut := out ++ afterLength.take llen
      let rest := afterLength.drop llen
      if rest.isEmpty then
        match lastStart with
        | none => some nextOut
        | some start =>
          if llen ≥ 5 ∧ start + 12 ≤ nextOut.length then some nextOut else none
      else
        match rest with
        | lo :: hi :: tail => do
          let offset := lo + 256 * hi
          if offset = 0 ∨ offset > nextOut.length then none else do
            let (extra, remaining) ← fieldLength (token % 16) tail
            sequences k remaining (matchCopy (extra + 4) offset nextOut)
              (some nextOut.length)
        | _ => none

def specDecode (block : List Nat) : Option (List Nat) :=
  if block.all (· < 256) then sequences (block.length + 1) block [] none else none

def encoderInput : List Nat := [97,98,99,100,97,98,99,100,69,70,71,72,73]
def encoderBlock : List Nat := [64,97,98,99,100,4,0,80,69,70,71,72,73]
def validBlock : List Nat := [19,97,1,0,80,98,99,100,101,102]
def validContent : List Nat := [97,97,97,97,97,97,97,97,98,99,100,101,102]
def emptyBlock : List Nat := [0]

theorem encoder_block_invalid : specDecode encoderBlock = none := rfl
theorem late_match : ¬ (4 + 12 ≤ encoderInput.length) := by decide
theorem valid_block_content : specDecode validBlock = some validContent := rfl
theorem valid_content_length : validContent.length = 13 := rfl
theorem empty_block_content : specDecode emptyBlock = some [] := rfl
theorem wrong_return : (1 : Nat) ≠ validContent.length := by decide
theorem outside_block : ¬ (65535 ≤ (65536 : Nat) ∧ 65536 < 65535 + 1) := by decide

end Verification
