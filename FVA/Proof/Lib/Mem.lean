import FVA.Proof.Lib.Walk
import FVA.Spec.CAbi

/-!
# Memory reads of caller-written bytes (U8 L4)

`ReturnsAfterWrite` claims start from a memory whose bytes at `p` are the caller's; a load inside
that range reads them back, and a `le32s` array reads as its elements.
-/

namespace FVA.Wasm.Exec

open FVA.Wasm

@[simp] theorem Store.withBytes_funcs (s : Store) (p : Nat) (bs : List UInt8) :
    (s.withBytes p bs).funcs = s.funcs := rfl

theorem Store.withBytes_mem0 {s : Store} {mem : MemInst} (h : s.mems[0]? = some mem) (p : Nat)
    (bs : List UInt8) : (s.withBytes p bs).mems[0]? = some (mem.withBytes p bs) := by
  simp [Store.withBytes, h]

@[simp] theorem MemInst.withBytes_pages (mem : MemInst) (p : Nat) (bs : List UInt8) :
    (mem.withBytes p bs).pages = mem.pages := rfl

@[simp] theorem MemInst.withBytes_size (mem : MemInst) (p : Nat) (bs : List UInt8) :
    (mem.withBytes p bs).size = mem.size := rfl

theorem le32s_length (xs : List (BitVec 32)) : (le32s xs).length = 4 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [le32s, List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih]; simp [le32]; omega

theorem le32s_getElem? (xs : List (BitVec 32)) (i k : Nat) (hk : k < 4) :
    (le32s xs)[4 * i + k]? = xs[i]?.map fun x => UInt8.ofNat (x.toNat / 256 ^ k) := by
  induction xs generalizing i with
  | nil => simp [le32s]
  | cons x xs ih =>
    have hl : (le32 x).length = 4 := by simp [le32]
    rcases i with _ | i
    · simp only [le32s, List.flatMap_cons, Nat.mul_zero, Nat.zero_add] at ih ⊢
      rw [List.getElem?_append_left (by omega)]
      simp [le32, List.getElem?_map, List.getElem?_range hk]
    · simp only [le32s, List.flatMap_cons] at ih ⊢
      rw [List.getElem?_append_right (by omega), hl,
        show 4 * (i + 1) + k - 4 = 4 * i + k by omega, ih]
      simp

/-- Four bytes of `x`, least significant first, are `x`. -/
theorem le32_digits (x : Nat) (h : x < 2 ^ 32) :
    x % 256 + 256 * (x / 256 % 256 + 256 * (x / 65536 % 256 + 256 * (x / 16777216 % 256 +
      256 * 0))) = x := by
  omega

/-- A 32-bit load inside a caller-written `le32s` array reads its element. -/
theorem read_le32s (mem : MemInst) {p i : Nat} {xs : List (BitVec 32)} (hi : i < xs.length) :
    (mem.withBytes p (le32s xs)).read (p + 4 * i) 4 = xs[i].toNat := by
  have hb : ∀ k < 4, (mem.withBytes p (le32s xs)).byte (p + 4 * i + k) =
      UInt8.ofNat (xs[i].toNat / 256 ^ k) := by
    intro k hk
    simp only [MemInst.withBytes, le32s_length]
    rw [ite_eq_left (by omega), show p + 4 * i + k - p = 4 * i + k by omega,
      List.getElem!_eq_getElem?_getD, le32s_getElem? xs i k hk, List.getElem?_eq_getElem hi]
    rfl
  have h0 := hb 0 (by decide)
  have h1 := hb 1 (by decide)
  have h2 := hb 2 (by decide)
  have h3 := hb 3 (by decide)
  simp only [Nat.add_zero] at h0
  show (MemInst.byte _ (p + 4 * i)).toNat + 256 * ((MemInst.byte _ (p + 4 * i + 1)).toNat +
    256 * ((MemInst.byte _ (p + 4 * i + 2)).toNat + 256 * ((MemInst.byte _ (p + 4 * i + 3)).toNat
      + 256 * 0))) = _
  rw [h0, h1, h2, h3]
  simp only [Nat.pow_zero, Nat.div_one, Nat.reducePow]
  exact le32_digits _ xs[i].isLt

end FVA.Wasm.Exec
