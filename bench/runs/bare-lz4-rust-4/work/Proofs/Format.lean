import Mathlib.Tactic

namespace LZ4Verification

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Reference length parser: every 255 requires another byte, including the
mandatory zero extension for an exact length of 15 (or a match of 19). -/
def extension : Nat → List Nat → Option (Nat × List Nat)
  | 0, _ => none
  | _+1, [] => none
  | fuel+1, b :: bs =>
    if b > 255 then none else
    if b == 255 then do
      let (n, rest) ← extension fuel bs
      return (255+n, rest)
    else some (b, bs)

/-- Byte-at-a-time copying gives the specified semantics for overlapping matches.
It rejects both zero offsets and references before the start of this block. -/
def copyMatch : Nat → Nat → List Nat → Option (List Nat)
  | 0, _, out => some out
  | n+1, offset, out => do
    if offset == 0 || offset > out.length then none else do
      let b ← out[out.length-offset]?
      copyMatch n offset (out ++ [b])

theorem copyMatch_length (n offset : Nat) (out result : List Nat)
    (h : copyMatch n offset out = some result) :
    result.length = out.length + n := by
  induction n generalizing out with
  | zero => simp [copyMatch] at h; subst result; omega
  | succ n ih =>
    simp only [copyMatch] at h
    split at h <;> simp_all
    rename_i hoff
    have hpos : offset > 0 := by omega
    have hle : offset ≤ out.length := by omega
    have hi : out.length - offset < out.length := by omega
    simp only [List.getElem?_eq_getElem hi, Option.bind_some] at h
    have hh := ih (out ++ [out[out.length-offset]]) h
    simp only [List.length_append, List.length_singleton] at hh
    omega

theorem copyMatch_prefix (n offset : Nat) (out result : List Nat)
    (h : copyMatch n offset out = some result) :
    out.IsPrefix result := by
  induction n generalizing out with
  | zero => simp [copyMatch] at h; subst result; exact ⟨[], by simp⟩
  | succ n ih =>
    simp only [copyMatch] at h
    split at h <;> simp_all
    rename_i hoff
    have hpos : offset > 0 := by omega
    have hle : offset ≤ out.length := by omega
    have hi : out.length - offset < out.length := by omega
    simp only [List.getElem?_eq_getElem hi, Option.bind_some] at h
    exact List.IsPrefix.trans (List.prefix_append _ _) (ih _ h)

structure Decoded where
  output : List Nat
  matchStarts : List Nat
  finalLiterals : Nat
  deriving Repr, DecidableEq

/-- Independent-block reference decoder, without imposing the end restrictions.
The fuel bounds sequence count, not length; each sequence consumes a token. -/
def decodeSequences : Nat → List Nat → List Nat → List Nat → Option Decoded
  | 0, _, _, _ => none
  | _+1, [], _, _ => none
  | fuel+1, token :: rest, out, starts => do
    if token > 255 then none else do
      let (lit, rest) ← if token / 16 == 15 then do
        let (n, r) ← extension (rest.length+1) rest
        pure (15+n, r)
      else pure (token / 16, rest)
      if lit > rest.length then none else do
        let out := out ++ rest.take lit
        let rest := rest.drop lit
        if rest.isEmpty then return ⟨out, starts, lit⟩ else
          match rest with
          | lo :: hi :: rest => do
            if lo > 255 || hi > 255 then none else do
              let offset := lo + 256*hi
              if offset == 0 || offset > out.length then none else do
                let (len, rest) ← if token % 16 == 15 then do
                  let (n, r) ← extension (rest.length+1) rest
                  pure (19+n, r)
                else pure (4+token%16, rest)
                let copied ← copyMatch len offset out
                decodeSequences fuel rest copied (starts ++ [out.length])
          | _ => none

def decode (input : List Nat) : Option Decoded :=
  decodeSequences (input.length+1) input [] []

/-- The three end restrictions, checked in addition to sequence parsing.
An empty decoded block is encoded by a token, not by an empty compressed input. -/
def endConditions (d : Decoded) : Bool :=
  (d.finalLiterals ≥ 5 || (d.matchStarts.isEmpty && d.output.length < 5)) &&
  d.matchStarts.all (fun p => p+12 ≤ d.output.length)

/-- An auxiliary arithmetic fact relevant to 32-bit length accumulators.
The caller region has 1,966,080 bytes. Even if every input byte contributed 255
to one length, adding the largest fixed length base cannot wrap a Wasm i32. -/
theorem length_accumulator_no_wrap (n len : Nat)
    (hn : n ≤ 1966080) (hlen : len ≤ 255*n + 19) :
    len < 4294967296 := by omega

end LZ4Verification
