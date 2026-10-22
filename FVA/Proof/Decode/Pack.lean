import FVA.Spec.Binary.Types

/-!
# Packed bytes

`pack` is the numeral `decode` reads; these lemmas turn the decoder's `Nat.land`/`Nat.shiftRight`
steps into list operations. T4: `pack` with the length determines the bytes.
-/

namespace FVA.Wasm.Binary

@[simp] theorem pack_nil : pack [] = 0 := rfl

theorem pack_cons (b : UInt8) (bs : List UInt8) : pack (b :: bs) = b.toNat + 256 * pack bs :=
  rfl

theorem pack_lt (bs : List UInt8) : pack bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    have := b.toNat_lt
    simp only [pack_cons, List.length_cons, Nat.pow_succ]
    omega

theorem pack_append (xs ys : List UInt8) :
    pack (xs ++ ys) = pack xs + 256 ^ xs.length * pack ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, pack_cons, ih, List.length_cons, Nat.pow_succ, Nat.mul_add]
    rw [Nat.mul_comm (256 ^ xs.length) 256, Nat.mul_assoc, Nat.add_assoc]

theorem two_pow_eight_mul (k : Nat) : 2 ^ (8 * k) = 256 ^ k := by rw [Nat.pow_mul]

/-- The low byte of a packed list is its head. -/
theorem land_pack_cons (b : UInt8) (bs : List UInt8) : Nat.land (pack (b :: bs)) 255 = b.toNat := by
  have := b.toNat_lt
  rw [Nat.land_eq, show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [pack_cons]
  omega

/-- Shifting out the low byte leaves the tail. -/
theorem shiftRight_pack_cons (b : UInt8) (bs : List UInt8) :
    Nat.shiftRight (pack (b :: bs)) 8 = pack bs := by
  have := b.toNat_lt
  rw [show Nat.shiftRight (pack (b :: bs)) 8 = pack (b :: bs) >>> 8 from rfl,
    Nat.shiftRight_eq_div_pow]
  simp only [pack_cons]
  omega

/-- The low `k` bytes of `pack (xs ++ ys)`, `k = xs.length`, are `pack xs`. -/
theorem land_pack_append (xs ys : List UInt8) :
    Nat.land (pack (xs ++ ys)) (Nat.pow 2 (8 * xs.length) - 1) = pack xs := by
  rw [Nat.land_eq, show Nat.pow 2 (8 * xs.length) = 2 ^ (8 * xs.length) from rfl,
    Nat.and_two_pow_sub_one_eq_mod, pack_append, two_pow_eight_mul, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (pack_lt xs)

/-- Shifting out `k = xs.length` bytes of `pack (xs ++ ys)` leaves `pack ys`. -/
theorem shiftRight_pack_append (xs ys : List UInt8) :
    Nat.shiftRight (pack (xs ++ ys)) (8 * xs.length) = pack ys := by
  rw [show Nat.shiftRight (pack (xs ++ ys)) (8 * xs.length) = pack (xs ++ ys) >>> (8 * xs.length)
    from rfl, Nat.shiftRight_eq_div_pow, pack_append, two_pow_eight_mul]
  have hp : 0 < 256 ^ xs.length := Nat.pow_pos (by decide)
  rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (pack_lt xs), Nat.zero_add]

/-- T4 (round trip): `leBytes` with the length recovers the bytes. -/
theorem leBytes_pack (bs : List UInt8) : leBytes bs.length (pack bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have := b.toNat_lt
    simp only [List.length_cons, leBytes, pack_cons]
    rw [show (b.toNat + 256 * pack bs) % 256 = b.toNat by omega,
      show (b.toNat + 256 * pack bs) / 256 = pack bs by omega, ih, Nat.toUInt8_eq,
      UInt8.ofNat_toNat]

/-- T4: equal lengths and equal packings mean equal bytes. -/
theorem pack_injective {xs ys : List UInt8} (hl : xs.length = ys.length) (hp : pack xs = pack ys) :
    xs = ys := by
  rw [← leBytes_pack xs, ← leBytes_pack ys, hl, hp]

end FVA.Wasm.Binary
