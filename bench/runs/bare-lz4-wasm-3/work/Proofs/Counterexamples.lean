import Mathlib.Data.List.Basic

/- A specification of independent LZ4 blocks, using unbounded natural lengths.
   This is a format model, not a model of the Wasm implementation. -/
namespace LZ4

structure Sequence where
  literals : List Nat
  matchInfo : Option (Nat × Nat) -- (offset, length); none for the final sequence
  deriving DecidableEq, Repr

-- Each 255 extends the field; a smaller byte terminates it (including zero).
def extension (base : Nat) : List Nat → Option (Nat × List Nat)
  | [] => none
  | b :: bs => if b = 255 then extension (base + b) bs else some (base + b, bs)

def lengthField (n : Nat) (bs : List Nat) : Option (Nat × List Nat) :=
  if n = 15 then extension n bs else some (n, bs)

-- Fuel bounds the number of sequences by the number of compressed bytes.
def parseSequences : Nat → List Nat → Option (List Sequence)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, token :: bs => do
    let (llen, rest) ← lengthField (token / 16) bs
    if llen > rest.length then none else do
      let literals := rest.take llen
      let tail := rest.drop llen
      if tail.isEmpty then
        some [⟨literals, none⟩]
      else
        match tail with
        | lo :: hi :: more => do
          let (mlen, next) ← lengthField (token % 16) more
          let sequences ← parseSequences fuel next
          some (⟨literals, some (lo + 256 * hi, mlen + 4)⟩ :: sequences)
        | _ => none

def parse (bytes : List Nat) : Option (List Sequence) :=
  if bytes.all (fun b => b < 256) then parseSequences (bytes.length + 1) bytes else none

-- Byte-at-a-time copying gives the specified meaning to overlapping matches.
def copyMatch : Nat → Nat → List Nat → List Nat
  | 0, _, out => out
  | n + 1, offset, out => copyMatch n offset (out ++ [out[out.length - offset]!])

structure Expanded where
  content : List Nat
  lastMatchStart : Option Nat
  finalLiteralCount : Nat
  deriving DecidableEq, Repr

def expandSequences : List Sequence → List Nat → Option Nat → Option Expanded
  | [], _, _ => none
  | [⟨lits, none⟩], out, last => some ⟨out ++ lits, last, lits.length⟩
  | ⟨lits, some (offset, mlen)⟩ :: rest, out, _ =>
    let prior := out ++ lits
    if offset = 0 ∨ offset > prior.length then none
    else expandSequences rest (copyMatch mlen offset prior) (some prior.length)
  | _, _, _ => none

def expand (bytes : List Nat) : Option Expanded := do
  let sequences ← parse bytes
  expandSequences sequences [] none

-- End conditions 1 and 2: final sequence is literal-only, with at least five
-- literals unless it is the sole sequence. Condition 1 is enforced by expansion.
-- Condition 3: the last match starts at least twelve decoded bytes before end.
def endConditions (e : Expanded) : Bool :=
  match e.lastMatchStart with
  | none => true
  | some start => e.finalLiteralCount ≥ 5 && start + 12 ≤ e.content.length

def validDecode (bytes : List Nat) : Option (List Nat) := do
  let e ← expand bytes
  if endConditions e then some e.content else none

def encoderInput : List Nat := [97, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98]
def encoderBlock : List Nat := [34, 97, 98, 1, 0, 80, 98, 98, 98, 98, 98]
def nonemptyBlock : List Nat := [19, 97, 1, 0, 80, 98, 99, 100, 101, 102]
def nonemptyContent : List Nat := [97, 97, 97, 97, 97, 97, 97, 97, 98, 99, 100, 101, 102]

theorem encoder_block_expands :
    expand encoderBlock = some ⟨encoderInput, some 2, 5⟩ := by rfl

theorem encoder_block_violates_end_condition :
    ¬ (2 + 12 ≤ encoderInput.length) := by decide

theorem encoder_block_invalid : validDecode encoderBlock = none := by rfl

theorem empty_block_valid : validDecode [0] = some [] := by rfl

theorem nonempty_block_valid :
    validDecode nonemptyBlock = some nonemptyContent := by rfl

theorem nonempty_decoded_length : nonemptyContent.length = 13 := by decide

end LZ4
