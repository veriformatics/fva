/-!
# LEB128 integers (reviewed spec)

Transcribes the Wasm 2.0 binary-format rules for `uN` and `sN` (spec §5.2.2) as relations
between a value and the complete byte list encoding it. Length and unused-bit limits come
from the side conditions exactly as the spec states them; non-minimal encodings within
those limits are allowed, as in the spec.
-/

namespace FVA.Wasm.Binary

/-- `ULeb N n bs`: the bytes `bs` encode the unsigned `N`-bit integer `n`. -/
inductive ULeb : Nat → Nat → List UInt8 → Prop where
  /-- `n:byte ⇒ n` if `n < 2^7 ∧ n < 2^N`. -/
  | last {N : Nat} (b : UInt8) (h7 : b.toNat < 2 ^ 7) (hN : b.toNat < 2 ^ N) :
      ULeb N b.toNat [b]
  /-- `n:byte m:u(N−7) ⇒ 2^7·m + (n − 2^7)` if `n ≥ 2^7 ∧ N > 7`. -/
  | more {N m : Nat} {rest : List UInt8} (b : UInt8) (h7 : 2 ^ 7 ≤ b.toNat) (hN : 7 < N)
      (hm : ULeb (N - 7) m rest) :
      ULeb N (2 ^ 7 * m + (b.toNat - 2 ^ 7)) (b :: rest)

/-- `SLeb N i bs`: the bytes `bs` encode the signed `N`-bit integer `i`. -/
inductive SLeb : Nat → Int → List UInt8 → Prop where
  /-- `n:byte ⇒ n` if `n < 2^6 ∧ n < 2^(N−1)`. -/
  | pos {N : Nat} (b : UInt8) (h6 : b.toNat < 2 ^ 6) (hN : b.toNat < 2 ^ (N - 1)) :
      SLeb N b.toNat [b]
  /-- `n:byte ⇒ n − 2^7` if `2^6 ≤ n < 2^7 ∧ n ≥ 2^7 − 2^(N−1)`. -/
  | neg {N : Nat} (b : UInt8) (h6 : 2 ^ 6 ≤ b.toNat) (h7 : b.toNat < 2 ^ 7)
      (hN : (2 ^ 7 : Int) - 2 ^ (N - 1) ≤ b.toNat) :
      SLeb N ((b.toNat : Int) - 2 ^ 7) [b]
  /-- `n:byte m:s(N−7) ⇒ 2^7·m + (n − 2^7)` if `n ≥ 2^7 ∧ N > 7`. -/
  | more {N : Nat} {m : Int} {rest : List UInt8} (b : UInt8) (h7 : 2 ^ 7 ≤ b.toNat)
      (hN : 7 < N) (hm : SLeb (N - 7) m rest) :
      SLeb N (2 ^ 7 * m + ((b.toNat : Int) - 2 ^ 7)) (b :: rest)

end FVA.Wasm.Binary
