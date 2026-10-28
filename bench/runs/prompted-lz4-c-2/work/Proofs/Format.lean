/- Independent block-format specification, from lz4_Block_format.md.
   Bytes are Nat values in [0,255]; returned none means malformed. -/
namespace Format

def extension : Nat → List Nat → Option (Nat × List Nat)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, b :: bs =>
    if b > 255 then none else
    if b < 255 then some (b, bs) else do
      let (n, rest) ← extension fuel bs
      pure (255 + n, rest)

def lengthField (fuel n : Nat) (bytes : List Nat) : Option (Nat × List Nat) :=
  if n < 15 then some (n, bytes) else do
    let (extra, rest) ← extension fuel bytes
    pure (15 + extra, rest)

def matchBytes (out : List Nat) (offset length : Nat) : List Nat :=
  if offset == 0 then List.replicate length 0 else
    (List.range length).map fun i => out[out.length - offset + i % offset]!

/- lastMatch is the output position at which the last match began. -/
def sequences (allowZero checkEnd : Bool) :
    Nat → List Nat → List Nat → Option Nat → Option (List Nat)
  | 0, _, _, _ => none
  | _ + 1, [], _, _ => none
  | fuel + 1, token :: bytes, out, lastMatch => do
    if token > 255 then none else do
      let (litlen, rest) ← lengthField (fuel + 1) (token / 16) bytes
      if rest.length < litlen then none else do
        let literals := rest.take litlen
        if !(literals.all (· < 256)) then none else do
          let out := out ++ literals
          let rest := rest.drop litlen
          if rest.isEmpty then
            if !checkEnd then some out else
              match lastMatch with
              | none => some out
              | some pos => if litlen ≥ 5 && out.length ≥ pos + 12 then some out else none
          else do
            let lo :: hi :: rest := rest | none
            if lo > 255 || hi > 255 then none else do
              let offset := lo + 256 * hi
              if offset > out.length || (!allowZero && offset == 0) then none else do
                let (len, rest) ← lengthField (fuel + 1) (token % 16) rest
                sequences allowZero checkEnd fuel rest
                  (out ++ matchBytes out offset (len + 4)) (some out.length)

def decode (allowZero checkEnd : Bool) (bytes : List Nat) : Option (List Nat) :=
  sequences allowZero checkEnd (bytes.length + 1) bytes [] none
end Format
