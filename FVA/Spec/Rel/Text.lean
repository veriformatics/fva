import FVA.Spec.Cert
import Mathlib.Data.Nat.Digits.Defs

/-! # Numbers as text, shared by the certificate relations (reviewed once; contract U9 B2) -/

namespace FVA.Cert

/-- The decimal digits of `n`, most significant first, as ASCII bytes (`0` = byte 48); zero is
the one digit `0`. -/
def decimal (n : Nat) : List UInt8 :=
  if n = 0 then [48] else (Nat.digits 10 n).reverse.map fun d => (48 + d).toUInt8

end FVA.Cert
