import FVA.Spec.CAbi

/-! Executable specification of the supplied LZ4 block format, including its three
end conditions. No decoder implementation is imported here. -/
namespace Proofs.Format

/-- Read the extension bytes, including the terminating byte below 255. -/
def extension (n : Nat) : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bs => if b.toNat = 255 then extension (n + 255) bs else some (n + b.toNat, bs)

/-- Nibble 15 requires extension bytes; smaller nibbles are the length. -/
def lengthField (n : Nat) (bs : List UInt8) : Option (Nat × List UInt8) :=
  if n = 15 then extension 15 bs else some (n, bs)

/-- A match is copied left to right, permitting overlap. -/
def matchCopy (offset : Nat) : Nat → List UInt8 → List UInt8
  | 0, out => out
  | n + 1, out => matchCopy offset n (out ++ [out[out.length - offset]!])

/-- Parse sequences; fuel bounds the number of tokens, each of which consumes a byte.
The last sequence has no offset. Its last five bytes must be literal (except for
an entire input shorter than five), and the last match starts at least 12 bytes
before the decoded end. Offsets must refer to already produced bytes. -/
def sequences : Nat → List UInt8 → List UInt8 → Option Nat → Option (List UInt8)
  | 0, _, _, _ => none
  | _ + 1, [], _, _ => none
  | fuel + 1, token :: bs, out, lastMatch => do
      let (llen, bs) ← lengthField (token.toNat / 16) bs
      if llen > bs.length then none else do
        let out := out ++ bs.take llen
        let bs := bs.drop llen
        if bs.isEmpty then
          if (out.length < 5 ∨ llen ≥ 5) ∧
              lastMatch.all (fun start => decide (start + 12 ≤ out.length))
          then some out else none
        else do
          let lo ← bs[0]?
          let hi ← bs[1]?
          let offset := lo.toNat + 256 * hi.toNat
          if offset = 0 ∨ offset > out.length then none else do
            let (mlen, bs) ← lengthField (token.toNat % 16) (bs.drop 2)
            sequences fuel bs (matchCopy offset (mlen + 4) out) (some out.length)

/-- Decode a complete independent block, rejecting violations of the block format. -/
def decode (bs : List UInt8) : Option (List UInt8) := sequences bs.length bs [] none

end Proofs.Format
