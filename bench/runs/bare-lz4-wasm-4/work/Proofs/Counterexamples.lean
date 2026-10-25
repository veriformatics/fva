import Mathlib.Tactic

/-! Specification facts about the concrete counterexamples.

This is a block-format model, not a model of WebAssembly. `verification/check.py`
checks the corresponding observations by executing the original binary.
Lengths/positions are natural numbers, bytes are checked to be below 256.
-/
namespace LZ4

structure Parsed where
  content : List Nat
  finalLiterals : Nat
  matchStarts : List Nat
  deriving DecidableEq, Repr

/-- Read the extension bytes following a nibble equal to 15. -/
def extension : Nat → List Nat → Option (Nat × List Nat)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, b :: rest =>
      if b = 255 then do
        let (n, tail) ← extension fuel rest
        pure (255 + n, tail)
      else pure (b, rest)

/-- Length excluding the match's mandatory four bytes. -/
def lengthField (nibble : Nat) (input : List Nat) : Option (Nat × List Nat) :=
  if nibble < 15 then some (nibble, input)
  else do
    let (extra, rest) ← extension (input.length + 1) input
    pure (15 + extra, rest)

/-- Sequential copying, including matches whose source overlaps their output. -/
def copyMatch : Nat → Nat → List Nat → Option (List Nat)
  | 0, _, output => some output
  | n + 1, offset, output => do
      let b ← output[output.length - offset]?
      copyMatch n offset (output ++ [b])

/-- Parse sequences and compute content and match-start positions.
The fuel is initially one more than the number of compressed bytes; every
recursive sequence consumes at least its token and two offset bytes. -/
def parseAux : Nat → List Nat → List Nat → List Nat → Option Parsed
  | 0, _, _, _ => none
  | _ + 1, [], _, _ => none
  | fuel + 1, token :: rest, output, starts => do
      let (llen, afterLength) ← lengthField (token / 16) rest
      if llen > afterLength.length then none else do
        let literals := afterLength.take llen
        let remaining := afterLength.drop llen
        let output := output ++ literals
        match remaining with
        | [] => pure ⟨output, llen, starts⟩
        | low :: high :: tail => do
            let offset := low + 256 * high
            if offset = 0 ∨ offset > output.length then none else do
              let (mlen, afterMatchLength) ← lengthField (token % 16) tail
              let copied ← copyMatch (mlen + 4) offset output
              parseAux fuel afterMatchLength copied (starts ++ [output.length])
        | _ => none

/-- Independent blocks: every match refers to content already in this block. -/
def parse (input : List Nat) : Option Parsed :=
  if input.all (fun b => b < 256) then
    parseAux (input.length + 1) input [] []
  else none

/-- The terminal sequence is literal-only by construction of `parseAux`.
For inputs shorter than five decoded bytes it must be the only sequence;
otherwise at least five trailing bytes are literal. Each match must start
at least twelve decoded bytes before the end. -/
def EndConditions (r : Parsed) : Prop :=
  (if r.content.length < 5 then
    r.matchStarts = [] ∧ r.finalLiterals = r.content.length
   else 5 ≤ r.finalLiterals) ∧
  r.matchStarts.all (fun start => start + 12 ≤ r.content.length) = true

instance (r : Parsed) : Decidable (EndConditions r) := by
  unfold EndConditions
  infer_instance

def ValidBlock (input : List Nat) : Prop :=
  match parse input with
  | none => False
  | some r => EndConditions r

def r1Input : List Nat := [97, 98, 99, 100, 97, 98, 99, 100, 49, 50, 51, 52, 53]
def r1Block : List Nat := [64, 97, 98, 99, 100, 4, 0, 80, 49, 50, 51, 52, 53]

/-- The raw sequences reconstruct the input, but their last match starts at 4. -/
theorem r1_parse : parse r1Block = some ⟨r1Input, 5, [4]⟩ := by decide

/-- The returned block violates a mandatory end condition. -/
theorem r1_invalid : ¬ ValidBlock r1Block := by
  unfold ValidBlock
  rw [r1_parse]
  decide

theorem r1_match_too_late : ¬ (4 + 12 ≤ r1Input.length) := by decide

def r2Block : List Nat := [19, 97, 1, 0, 80, 98, 99, 100, 101, 102]
def r2Content : List Nat := [97, 97, 97, 97, 97, 97, 97, 97, 98, 99, 100, 101, 102]

/-- One literal, an offset-one match of length seven, and five final literals. -/
theorem r2_parse : parse r2Block = some ⟨r2Content, 5, [1]⟩ := by decide

theorem r2_valid : ValidBlock r2Block := by
  unfold ValidBlock
  rw [r2_parse]
  decide

theorem r2_expected_length : r2Content.length = 13 := by decide

theorem r2_return_wrong : (1 : Nat) ≠ r2Content.length := by decide

theorem empty_parse : parse [0] = some ⟨[], 0, []⟩ := by decide

theorem empty_valid : ValidBlock [0] := by
  unfold ValidBlock
  rw [empty_parse]
  decide

/-- The empty block fits in the last byte of a one-page memory. -/
theorem empty_block_fits : (65535 : Nat) + [0].length = 65536 := by decide

/-- The first attempted offset load is outside both the block and memory. -/
theorem empty_offset_outside :
    ¬ ((65536 : Nat) < 65535 + [0].length) ∧ ¬ ((65536 : Nat) < 65536) := by decide

#print axioms r1_parse
#print axioms r1_invalid
#print axioms r1_match_too_late
#print axioms r2_parse
#print axioms r2_valid
#print axioms r2_expected_length
#print axioms r2_return_wrong
#print axioms empty_parse
#print axioms empty_valid
#print axioms empty_block_fits
#print axioms empty_offset_outside

end LZ4
