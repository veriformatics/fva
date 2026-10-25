import Mathlib.Data.List.Basic

/- An executable specification of independent LZ4 blocks, using unbounded
   natural lengths. This models the format, not the Wasm implementation.
   Bytes are natural numbers checked to be < 256. -/
namespace LZ4

def extension : List Nat → Option (Nat × List Nat)
  | [] => none
  | b :: bs =>
    if b ≥ 256 then none
    else if b = 255 then do
      let (n, rest) ← extension bs
      pure (255 + n, rest)
    else some (b, bs)

def lengthField (n : Nat) (bs : List Nat) : Option (Nat × List Nat) :=
  if n < 15 then some (n, bs)
  else if n = 15 then do
    let (extra, rest) ← extension bs
    pure (15 + extra, rest)
  else none

-- Copy one byte at a time, so overlapping matches use newly produced bytes.
def matchCopy (offset : Nat) : Nat → List Nat → List Nat
  | 0, out => out
  | n + 1, out => matchCopy offset n (out ++ [out.getD (out.length - offset) 0])

-- Fuel only bounds the number of sequences, not lengths or output size.
-- Every sequence consumes a token, so input.length + 1 is sufficient.
def parse : Nat → List Nat → List Nat → Option Nat → Option (List Nat)
  | 0, _, _, _ => none
  | _ + 1, [], _, _ => none
  | fuel + 1, token :: bytes, out, lastMatch => do
    if token ≥ 256 then none else do
      let (llen, rest) ← lengthField (token / 16) bytes
      if llen > rest.length then none else do
        let literals := rest.take llen
        if literals.any (· ≥ 256) then none else do
          let after := out ++ literals
          let rest := rest.drop llen
          if rest.isEmpty then
            -- End rules 1 and 2: literal-only final sequence, five literals,
            -- with a special single-sequence exception for lengths below five.
            if after.length < 5 then
              if lastMatch.isNone then some after else none
            else if literals.length < 5 then none
            else
              -- End rule 3: final match starts at least twelve bytes before end.
              match lastMatch with
              | none => some after
              | some start => if start + 12 ≤ after.length then some after else none
          else
            match rest with
            | lo :: hi :: tail => do
              if lo ≥ 256 ∨ hi ≥ 256 then none else do
                let offset := lo + 256 * hi
                if offset = 0 ∨ offset > after.length then none else do
                  let (mlen, tail) ← lengthField (token % 16) tail
                  parse fuel tail (matchCopy offset (mlen + 4) after) (some after.length)
            | _ => none

def decodeSpec (bytes : List Nat) : Option (List Nat) :=
  parse (bytes.length + 1) bytes [] none

def ValidBlock (bytes : List Nat) : Prop := ∃ content, decodeSpec bytes = some content

def encoderInput : List Nat := [65, 66, 67, 68, 69, 70, 71, 72, 65, 66, 67, 68, 69]
def encoderBlock : List Nat := [128, 65, 66, 67, 68, 69, 70, 71, 72, 8, 0, 16, 69]
def decoderBlock : List Nat := [19, 65, 1, 0, 80, 66, 67, 68, 69, 70]
def decoderContent : List Nat := [65, 65, 65, 65, 65, 65, 65, 65, 66, 67, 68, 69, 70]
def emptyBlock : List Nat := [0]

theorem encoder_block_rejected : decodeSpec encoderBlock = none := by decide

theorem encoder_block_invalid : ¬ ValidBlock encoderBlock := by
  rintro ⟨content, h⟩
  rw [encoder_block_rejected] at h
  contradiction

theorem decoder_block_content : decodeSpec decoderBlock = some decoderContent := by decide

theorem decoder_block_valid : ValidBlock decoderBlock :=
  ⟨decoderContent, decoder_block_content⟩

theorem decoder_content_length : decoderContent.length = 13 := by decide

theorem empty_block_content : decodeSpec emptyBlock = some [] := by decide

theorem empty_block_valid : ValidBlock emptyBlock := ⟨[], empty_block_content⟩

-- The encoder witness has only one trailing literal, and its match starts
-- eight bytes into thirteen decoded bytes: both end restrictions fail.
theorem encoder_end_rules_fail : ¬ (5 ≤ (1 : Nat)) ∧ ¬ (8 + 12 ≤ (13 : Nat)) := by decide

end LZ4

#print axioms LZ4.encoder_block_invalid
#print axioms LZ4.decoder_block_content
#print axioms LZ4.empty_block_content
