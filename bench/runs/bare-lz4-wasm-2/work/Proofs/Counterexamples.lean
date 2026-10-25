import Mathlib.Data.List.Basic

/-!
A specification interpreter for independent LZ4 blocks. This is NOT a model of
WebAssembly execution. Runtime assertions in verification/*.wast supply that
separate connection. Bytes are naturals, checked to be below 256 at entry.

The parser records decoded positions, rather than compressed-file positions,
for the last-match distance rule. Matching copies one byte at a time, so that
offset-one and other overlapping matches have their specified meaning.
-/
namespace LZ4

structure Trace where
  output : List Nat
  matchStarts : List Nat
  finalLiterals : Nat
  deriving DecidableEq, Repr

-- The nibble 15 requires at least one extension byte, even when it is zero.
def extension : List Nat → Option (Nat × List Nat)
  | [] => none
  | b :: bs =>
    if b = 255 then do
      let (n, rest) ← extension bs
      pure (255 + n, rest)
    else pure (b, bs)

def fieldLength (nibble : Nat) (bs : List Nat) : Option (Nat × List Nat) :=
  if nibble < 15 then some (nibble, bs)
  else do
    let (extra, rest) ← extension bs
    pure (15 + extra, rest)

-- Only called with 1 ≤ offset ≤ output.length.
def copyMatch : Nat → Nat → List Nat → List Nat
  | 0, _, output => output
  | n + 1, offset, output =>
    copyMatch n offset (output ++ [output[output.length - offset]!])

-- Each recursive sequence consumes at least its token; input.length + 1 fuel
-- is enough for every syntactically possible sequence in a finite input.
def sequences : Nat → List Nat → List Nat → List Nat → Option Trace
  | 0, _, _, _ => none
  | _ + 1, [], _, _ => none -- A block requires a final token, including empty input.
  | fuel + 1, token :: bs, output, starts => do
    let (literalLen, afterLen) ← fieldLength (token / 16) bs
    if literalLen > afterLen.length then none else do
      let afterLiterals := afterLen.drop literalLen
      let withLiterals := output ++ afterLen.take literalLen
      if afterLiterals.isEmpty then
        pure ⟨withLiterals, starts, literalLen⟩
      else
        match afterLiterals with
        | lo :: hi :: rest =>
          let offset := lo + 256 * hi
          if offset = 0 ∨ offset > withLiterals.length then none else do
            let (matchExtra, afterMatchLen) ← fieldLength (token % 16) rest
            sequences fuel afterMatchLen
              (copyMatch (4 + matchExtra) offset withLiterals)
              (starts ++ [withLiterals.length])
        | _ => none

def parseBlock (bs : List Nat) : Option Trace :=
  if bs.all (· < 256) then sequences (bs.length + 1) bs [] [] else none

-- End conditions from the supplied specification. A final-only short block
-- is permitted; every match, in particular the last, starts ≥12 bytes before
-- the decoded end. Earlier match positions are smaller, so testing all is
-- equivalent to testing the last one.
def endConditions (t : Trace) : Bool :=
  (t.finalLiterals ≥ 5 || (t.matchStarts.isEmpty && t.output.length < 5)) &&
    t.matchStarts.all (fun start => start + 12 ≤ t.output.length)

def checkBlock (bs : List Nat) : Bool :=
  match parseBlock bs with
  | none => false
  | some t => endConditions t

def ValidBlock (bs : List Nat) : Prop := checkBlock bs = true

-- These lists are the exact bytes asserted by the runtime harnesses.
def r1Input : List Nat := [97, 98, 97, 98, 97, 98, 97, 98, 97, 98, 97, 98, 99]
def r1Block : List Nat := [34, 97, 98, 2, 0, 80, 97, 98, 97, 98, 99]
def r2Block : List Nat := [19, 97, 1, 0, 80, 97, 97, 97, 97, 97]
def emptyBlock : List Nat := [0]

-- R1's emitted block round-trips under the syntax, but violates a mandatory
-- end condition. Refuting that one conjunct suffices to refute R1.
theorem r1_parse : parseBlock r1Block = some ⟨r1Input, [2], 5⟩ := by decide

theorem r1_last_match_too_late : ¬ (2 + 12 ≤ r1Input.length) := by decide

theorem r1_not_valid : ¬ ValidBlock r1Block := by unfold ValidBlock; decide

-- R2's witness is valid even with all three end restrictions enforced.
theorem r2_parse :
    parseBlock r2Block = some ⟨List.replicate 13 97, [1], 5⟩ := by decide

theorem r2_valid : ValidBlock r2Block := by unfold ValidBlock; decide

theorem r2_wrong_length : (1 : Nat) ≠ (List.replicate 13 97).length := by decide

theorem r2_wrong_second_byte : (204 : Nat) ≠ (List.replicate 13 97)[1]! := by decide

-- R3 uses a valid block, so the failure does not depend on malformed input.
theorem empty_parse : parseBlock emptyBlock = some ⟨[], [], 0⟩ := by decide

theorem empty_valid : ValidBlock emptyBlock := by unfold ValidBlock; decide

-- Its sole supplied byte is in bounds; the immediately following byte is
-- both outside that block and outside a one-page WebAssembly memory.
theorem r3_boundary :
    65535 < 65536 ∧ 65535 + emptyBlock.length = 65536 ∧
    ¬ (65536 < 65535 + emptyBlock.length) ∧ ¬ (65536 < 65536) := by decide

end LZ4
