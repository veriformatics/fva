import FVA.Spec.Exec.Runtime

/-!
# Reads after writes (U14 S4)

The cell algebra a loop invariant over memory needs: a write leaves the size and every byte
outside its range unchanged, and reading back the bytes it wrote gives the stored value modulo
`256^k`. Loads and stores of `k`-byte values go through `MemInst.read` / `MemInst.write`.
-/

namespace FVA.Wasm.Exec

theorem MemInst.write_byte (m : MemInst) (ea k v a : Nat) :
    (m.write ea k v).byte a =
      if ea ≤ a ∧ a < ea + k then UInt8.ofNat (v / 256 ^ (a - ea)) else m.byte a := rfl

@[simp] theorem MemInst.write_pages (m : MemInst) (ea k v : Nat) :
    (m.write ea k v).pages = m.pages := rfl

@[simp] theorem MemInst.write_size (m : MemInst) (ea k v : Nat) :
    (m.write ea k v).size = m.size := rfl

@[simp] theorem MemInst.write_max (m : MemInst) (ea k v : Nat) :
    (m.write ea k v).max = m.max := rfl

/-- A read of `k'` bytes outside a write's `k` bytes sees the old contents. -/
theorem MemInst.read_write_of_disjoint (m : MemInst) {ea k v ea' k' : Nat}
    (h : ea' + k' ≤ ea ∨ ea + k ≤ ea') : (m.write ea k v).read ea' k' = m.read ea' k' := by
  induction k' generalizing ea' with
  | zero => rfl
  | succ k' ih =>
    have hn : ¬(ea ≤ ea' ∧ ea' < ea + k) := by omega
    simp only [MemInst.read, MemInst.write_byte, hn, ↓reduceIte, ih (ea' := ea' + 1) (by omega)]

/-- `k` bytes holding the little-endian digits of `v` read back as `v % 256^k`. -/
theorem MemInst.read_of_bytes (m : MemInst) {ea k v : Nat}
    (h : ∀ i, i < k → m.byte (ea + i) = UInt8.ofNat (v / 256 ^ i)) :
    m.read ea k = v % 256 ^ k := by
  induction k generalizing ea v with
  | zero => simp [MemInst.read, Nat.mod_one]
  | succ k ih =>
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero, Nat.pow_zero, Nat.div_one] at h0
    have hrest : ∀ i, i < k → m.byte (ea + 1 + i) = UInt8.ofNat (v / 256 / 256 ^ i) := by
      intro i hi
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ', Nat.add_assoc, Nat.add_comm 1 i]
      exact h (i + 1) (by omega)
    simp only [MemInst.read, h0, ih hrest]
    rw [Nat.pow_succ', Nat.mod_mul]
    simp

/-- Reading back the `k` bytes a write just stored gives the value modulo `256^k`. -/
theorem MemInst.read_write_self (m : MemInst) (ea k v : Nat) :
    (m.write ea k v).read ea k = v % 256 ^ k :=
  MemInst.read_of_bytes _ fun i hi => by
    have hp : ea ≤ ea + i ∧ ea + i < ea + k := by omega
    simp [MemInst.write_byte, hp]

end FVA.Wasm.Exec
