/-!
# Byte packing for `.wasm` files

`decode` reads a file as one little-endian numeral. Packing splits in halves so GMP work stays
`O(n log n)`; a byte-at-a-time fold, like Lean's own numeral parsing, is quadratic (decimal
literal of 96 KB: 28 s to elaborate).
-/

namespace FVA.Tool

/-- Little-endian packing of `bs[lo:hi]`. -/
def packRange (bs : ByteArray) (lo hi : Nat) : Nat :=
  if hi ≤ lo + 32 then
    (List.range (hi - lo)).foldr (fun i acc => acc * 256 + (bs.get! (lo + i)).toNat) 0
  else
    let mid := (lo + hi) / 2
    packRange bs lo mid + (packRange bs mid hi <<< (8 * (mid - lo)))
termination_by hi - lo

/-- Little-endian packing of file bytes, the representation `decode` reads. -/
def packBytes (bs : ByteArray) : Nat := packRange bs 0 bs.size

/-- Lowercase hex digits of the bytes, in file order. -/
def toHex (bs : ByteArray) : String :=
  let d (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'
  String.ofList (bs.toList.flatMap fun b => [d (b.toNat / 16), d (b.toNat % 16)])

/-- The value of a lowercase hex digit. -/
def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none

/-- Bytes from pairs of hex digits, appended to `acc`. -/
def ofHexAux : List Char → Array UInt8 → Option (Array UInt8)
  | [], acc => some acc
  | h :: l :: rest, acc => do
    ofHexAux rest (acc.push (16 * (← hexDigit h) + (← hexDigit l)).toUInt8)
  | [_], _ => none

/-- Bytes from hex digits in file order; `none` on an odd length or a non-hex character. -/
def ofHex (s : String) : Option ByteArray := (ofHexAux s.toList #[]).map (⟨·⟩)

end FVA.Tool
