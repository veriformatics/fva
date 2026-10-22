/-!
# Integer operations (reviewed spec)

Transcribes the WebAssembly 2.0 integer operations (spec §4.3.2) and integer conversions
(§4.3.4). Values are `BitVec N` read as unsigned numbers `0 ≤ i < 2^N`; each operation is written
as the spec states it, through `signed` and the inverse `ofSigned`, so a reviewer compares it
line by line with the spec text. A partial operation returns `none` where the spec says the
result is undefined (the instruction traps).
-/

namespace FVA.Wasm.Num

/-- `signed_N(i)`: the two's-complement reading of `i` (spec §4.3.1). -/
def signed {N : Nat} (i : BitVec N) : Int :=
  if i.toNat < 2 ^ (N - 1) then i.toNat else (i.toNat : Int) - 2 ^ N

/-- `signed_N⁻¹(j)`: the `N`-bit pattern of `j` (`j mod 2^N`). -/
def ofSigned (N : Nat) (j : Int) : BitVec N := BitVec.ofInt N j

/-- `bool(c)`: 1 if `c` holds, else 0, as an `i32`. -/
def bool (c : Bool) : BitVec 32 := if c then 1 else 0

variable {N : Nat}

/-- `iadd_N(i₁, i₂) = (i₁ + i₂) mod 2^N`. -/
def iadd (i₁ i₂ : BitVec N) : BitVec N := BitVec.ofNat N (i₁.toNat + i₂.toNat)

/-- `isub_N(i₁, i₂) = (i₁ − i₂ + 2^N) mod 2^N`. -/
def isub (i₁ i₂ : BitVec N) : BitVec N := BitVec.ofNat N (i₁.toNat + 2 ^ N - i₂.toNat)

/-- `imul_N(i₁, i₂) = (i₁ · i₂) mod 2^N`. -/
def imul (i₁ i₂ : BitVec N) : BitVec N := BitVec.ofNat N (i₁.toNat * i₂.toNat)

/-- `idiv_u_N(i₁, i₂)`: undefined if `i₂ = 0`, else `trunc(i₁ / i₂)`. -/
def idiv_u (i₁ i₂ : BitVec N) : Option (BitVec N) :=
  if i₂.toNat = 0 then none else some (BitVec.ofNat N (i₁.toNat / i₂.toNat))

/-- `idiv_s_N(i₁, i₂)`: undefined if `j₂ = 0` or `j₁ / j₂ = 2^(N−1)`, else
`signed⁻¹(trunc(j₁ / j₂))`, where `j = signed(i)`. -/
def idiv_s (i₁ i₂ : BitVec N) : Option (BitVec N) :=
  if signed i₂ = 0 then none
  else if (signed i₁).tdiv (signed i₂) = 2 ^ (N - 1) then none
  else some (ofSigned N ((signed i₁).tdiv (signed i₂)))

/-- `irem_u_N(i₁, i₂)`: undefined if `i₂ = 0`, else `i₁ − i₂ · trunc(i₁ / i₂)`. -/
def irem_u (i₁ i₂ : BitVec N) : Option (BitVec N) :=
  if i₂.toNat = 0 then none else some (BitVec.ofNat N (i₁.toNat % i₂.toNat))

/-- `irem_s_N(i₁, i₂)`: undefined if `i₂ = 0`, else `signed⁻¹(j₁ − j₂ · trunc(j₁ / j₂))`
(the sign of the dividend). -/
def irem_s (i₁ i₂ : BitVec N) : Option (BitVec N) :=
  if signed i₂ = 0 then none else some (ofSigned N ((signed i₁).tmod (signed i₂)))

/-- `iand`, `ior`, `ixor`: bitwise. -/
def iand (i₁ i₂ : BitVec N) : BitVec N := i₁ &&& i₂
/-- Bitwise or. -/
def ior (i₁ i₂ : BitVec N) : BitVec N := i₁ ||| i₂
/-- Bitwise exclusive or. -/
def ixor (i₁ i₂ : BitVec N) : BitVec N := i₁ ^^^ i₂

/-- `ishl_N(i₁, i₂) = (i₁ · 2^k) mod 2^N`, `k = i₂ mod N`. -/
def ishl (i₁ i₂ : BitVec N) : BitVec N := BitVec.ofNat N (i₁.toNat * 2 ^ (i₂.toNat % N))

/-- `ishr_u_N(i₁, i₂) = trunc(i₁ / 2^k)`, `k = i₂ mod N`. -/
def ishr_u (i₁ i₂ : BitVec N) : BitVec N := BitVec.ofNat N (i₁.toNat / 2 ^ (i₂.toNat % N))

/-- `ishr_s_N(i₁, i₂)`: the sign bit fills the vacated bits, i.e. `signed⁻¹(⌊j₁ / 2^k⌋)`. -/
def ishr_s (i₁ i₂ : BitVec N) : BitVec N :=
  ofSigned N ((signed i₁).fdiv (2 ^ (i₂.toNat % N)))

/-- `irotl_N(i₁, i₂)`: rotate left by `k = i₂ mod N`. -/
def irotl (i₁ i₂ : BitVec N) : BitVec N :=
  let k := i₂.toNat % N
  BitVec.ofNat N (i₁.toNat * 2 ^ k + i₁.toNat / 2 ^ (N - k))

/-- `irotr_N(i₁, i₂)`: rotate right by `k = i₂ mod N`. -/
def irotr (i₁ i₂ : BitVec N) : BitVec N :=
  let k := i₂.toNat % N
  BitVec.ofNat N (i₁.toNat / 2 ^ k + i₁.toNat * 2 ^ (N - k))

/-- Number of significant bits of a natural number (0 for 0). -/
def bitLength (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

/-- `iclz_N(i)`: leading zero bits (`N` for 0). -/
def iclz (i : BitVec N) : BitVec N := BitVec.ofNat N (N - bitLength i.toNat)

/-- Trailing zero bits of a positive number below `2^fuel`. -/
def trailingZeros : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n % 2 = 1 then 0 else trailingZeros fuel (n / 2) + 1

/-- `ictz_N(i)`: trailing zero bits (`N` for 0). -/
def ictz (i : BitVec N) : BitVec N :=
  BitVec.ofNat N (if i.toNat = 0 then N else trailingZeros N i.toNat)

/-- One bits of a number below `2^fuel`. -/
def ones : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => n % 2 + ones fuel (n / 2)

/-- `ipopcnt_N(i)`: the number of 1 bits. -/
def ipopcnt (i : BitVec N) : BitVec N := BitVec.ofNat N (ones N i.toNat)

/-- `ieqz_N(i) = bool(i = 0)`. -/
def ieqz (i : BitVec N) : BitVec 32 := bool (i.toNat == 0)
/-- `ieq_N(i₁, i₂) = bool(i₁ = i₂)`. -/
def ieq (i₁ i₂ : BitVec N) : BitVec 32 := bool (i₁.toNat == i₂.toNat)
/-- `ine_N(i₁, i₂) = bool(i₁ ≠ i₂)`. -/
def ine (i₁ i₂ : BitVec N) : BitVec 32 := bool (i₁.toNat != i₂.toNat)
/-- `ilt_u_N(i₁, i₂) = bool(i₁ < i₂)`. -/
def ilt_u (i₁ i₂ : BitVec N) : BitVec 32 := bool (decide (i₁.toNat < i₂.toNat))
/-- `ilt_s_N(i₁, i₂) = bool(signed(i₁) < signed(i₂))`. -/
def ilt_s (i₁ i₂ : BitVec N) : BitVec 32 := bool (decide (signed i₁ < signed i₂))
/-- `igt_u_N(i₁, i₂) = bool(i₁ > i₂)`. -/
def igt_u (i₁ i₂ : BitVec N) : BitVec 32 := bool (decide (i₁.toNat > i₂.toNat))
/-- `igt_s_N(i₁, i₂) = bool(signed(i₁) > signed(i₂))`. -/
def igt_s (i₁ i₂ : BitVec N) : BitVec 32 := bool (decide (signed i₁ > signed i₂))
/-- `ile_u_N(i₁, i₂) = bool(i₁ ≤ i₂)`. -/
def ile_u (i₁ i₂ : BitVec N) : BitVec 32 := bool (decide (i₁.toNat ≤ i₂.toNat))
/-- `ile_s_N(i₁, i₂) = bool(signed(i₁) ≤ signed(i₂))`. -/
def ile_s (i₁ i₂ : BitVec N) : BitVec 32 := bool (decide (signed i₁ ≤ signed i₂))
/-- `ige_u_N(i₁, i₂) = bool(i₁ ≥ i₂)`. -/
def ige_u (i₁ i₂ : BitVec N) : BitVec 32 := bool (decide (i₁.toNat ≥ i₂.toNat))
/-- `ige_s_N(i₁, i₂) = bool(signed(i₁) ≥ signed(i₂))`. -/
def ige_s (i₁ i₂ : BitVec N) : BitVec 32 := bool (decide (signed i₁ ≥ signed i₂))

/-- `iextendM_s_N(i) = signed_N⁻¹(signed_M(i mod 2^M))`. -/
def iextend_s (M : Nat) (i : BitVec N) : BitVec N :=
  ofSigned N (signed (BitVec.ofNat M i.toNat))

/-- `wrap_{64,32}(i) = i mod 2^32` (§4.3.4). -/
def wrap (i : BitVec 64) : BitVec 32 := BitVec.ofNat 32 i.toNat

/-- `extend_u_{32,64}(i) = i`. -/
def extend_u (i : BitVec 32) : BitVec 64 := BitVec.ofNat 64 i.toNat

/-- `extend_s_{32,64}(i) = signed_64⁻¹(signed_32(i))`. -/
def extend_s (i : BitVec 32) : BitVec 64 := ofSigned 64 (signed i)

end FVA.Wasm.Num
