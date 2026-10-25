import Init
namespace Verification.LZ4
-- Specification of the supplied block-format document, using unbounded lengths.
-- The compressed byte list is independent of the Wasm implementation.
def extension : List Nat → Nat → Option (Nat × List Nat)
  | [], _ => none
  | b :: bs, n => if b = 255 then extension bs (n+b) else some (n+b, bs)

def field (n : Nat) (bs : List Nat) : Option (Nat × List Nat) :=
  if n = 15 then extension bs n else some (n, bs)

-- Append one byte at a time, including overlapping matches.
def copy : Nat → Nat → List Nat → List Nat
  | 0, _, out => out
  | n+1, off, out => copy n off (out ++ [out[out.length-off]!])

def sequences : Nat → List Nat → List Nat → List Nat → Option (List Nat)
  | 0, _, _, _ => none
  | fuel+1, bytes, out, starts => do
    let t :: bs := bytes | none
    let (nl, bs) ← field (t / 16) bs
    if nl > bs.length then none else do
      let out' := out ++ bs.take nl
      let rest := bs.drop nl
      if rest.isEmpty then
        if (starts.isEmpty || decide (5 ≤ nl)) &&
           starts.all (fun p => decide (p+12 ≤ out'.length)) then some out' else none
      else do
        let lo :: hi :: rest := rest | none
        let off := lo + 256*hi
        if off = 0 || off > out'.length then none else do
          let (nm, rest) ← field (t % 16) rest
          sequences fuel rest (copy (nm+4) off out') (out'.length :: starts)

def decode (block : List Nat) : Option (List Nat) :=
  if block.all (fun b => decide (b < 256)) then
    sequences (block.length+1) block [] [] else none

def Valid (block decoded : List Nat) : Prop := decode block = some decoded
end Verification.LZ4
