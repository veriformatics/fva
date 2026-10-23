import FVA.Spec.Binary.Types

/-!
# Per-output certificates (reviewed once; contract U9 B1)

A certificate is a theorem `Accepted R i o`: the bytes of an output file stand in relation `R`
to the bytes of an input file. Each file enters Lean as a generated blob module (`fva blob`): a
numeral packing the file's bytes little-endian (`Binary.pack`) and their count, which
`fva trust` compares with the file on disk. Proof generation is untrusted: the kernel checks
the proof, and `R` is read like any spec.
-/

namespace FVA.Cert

open FVA.Wasm.Binary

/-- A file's bytes as one little-endian numeral and their count. -/
structure Blob where
  /-- The bytes, packed little-endian (`pack`). -/
  bytes : Nat
  /-- How many bytes (trailing zero bytes included). -/
  len : Nat

/-- The blob's bytes in file order. -/
def Blob.data (b : Blob) : List UInt8 := leBytes b.len b.bytes

/-- The output file's bytes stand in relation `R` to the input file's bytes. -/
def Accepted (R : List UInt8 → List UInt8 → Prop) (i o : Blob) : Prop := R i.data o.data

end FVA.Cert
