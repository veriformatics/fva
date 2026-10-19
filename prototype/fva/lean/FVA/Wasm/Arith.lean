import FVA.Wasm.Attr

/-!
# BitVec → Nat rewrites — proof support, outside the trusted base

Core proves `BitVec.toNat_add` & co. by `rfl` ⇒ `simp` applies them definitionally, leaving
the kernel to re-derive each step by unfolding `Nat.mod` on symbolic values (minutes per
large literal, or deep recursion). `id`-wrapped copies force explicit rewrite steps.
-/

namespace FVA.Wasm.Arith

variable {w : Nat} (x y : BitVec w)

@[wasm_arith] theorem toNat_add : (x + y).toNat = (x.toNat + y.toNat) % 2 ^ w := id (BitVec.toNat_add x y)
@[wasm_arith] theorem toNat_sub : (x - y).toNat = (2 ^ w - y.toNat + x.toNat) % 2 ^ w :=
  id (BitVec.toNat_sub x y)
@[wasm_arith] theorem toNat_mul : (x * y).toNat = x.toNat * y.toNat % 2 ^ w := id (BitVec.toNat_mul x y)
@[wasm_arith] theorem toNat_setWidth (v : Nat) : (x.setWidth v).toNat = x.toNat % 2 ^ v :=
  id (BitVec.toNat_setWidth v x)
@[wasm_arith] theorem toNat_ushiftRight (k : Nat) : (x >>> k).toNat = x.toNat / 2 ^ k :=
  id (by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow])
@[wasm_arith] theorem toNat_umod : (x % y).toNat = x.toNat % y.toNat := id BitVec.toNat_umod
@[wasm_arith] theorem toNat_ofNat (n : Nat) : (BitVec.ofNat w n).toNat = n % 2 ^ w :=
  id (BitVec.toNat_ofNat n w)

end FVA.Wasm.Arith
