import FVA.Proof.Lib.BlockEval
import FVA.Proof.Lib.Arith
import FVA.Proof.Lib.BlockAttr

namespace FVA.Wasm.Exec.Ref

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Num

theorem ofNat32_toNat {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n :=
  Nat.mod_eq_of_lt h

theorem ofNat32_eq_zero {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.ofNat 32 n = 0) ↔ n = 0 := by
  rw [← BitVec.toNat_inj, ofNat32_toNat h]; rfl

theorem add32 (a b : Nat) : iadd (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) =
    BitVec.ofNat 32 (a + b) := by rw [iadd_eq, BitVec.ofNat_add]

theorem add32_neg {a k : Nat} (h : k ≤ a) (hk : k ≤ 2 ^ 32) :
    iadd (BitVec.ofNat 32 a) (BitVec.ofNat 32 (2 ^ 32 - k)) = BitVec.ofNat 32 (a - k) := by
  rw [add32]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have he : a + (2 ^ 32 - k) = (a - k) + 2 ^ 32 := by omega
  rw [he, Nat.add_mod_right]

theorem ltU32 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    iltU (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = bool (decide (a < b)) := by
  simp only [iltU, ofNat32_toNat ha, ofNat32_toNat hb]

theorem ne32 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    ine (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = bool (decide (a ≠ b)) := by
  simp only [ine, ofNat32_toNat ha, ofNat32_toNat hb]
  congr 1

theorem eqz32 {a : Nat} (ha : a < 2 ^ 32) :
    ieqz (BitVec.ofNat 32 a) = bool (decide (a = 0)) := by
  simp only [ieqz, ofNat32_toNat ha]
  congr 1

theorem and32_low (a : Nat) : iand (BitVec.ofNat 32 a) (BitVec.ofNat 32 3) =
    BitVec.ofNat 32 (a % 4) := by
  change BitVec.ofNat 32 a &&& BitVec.ofNat 32 (2 ^ 2 - 1) = _
  rw [← BitVec.ofNat_and, Nat.and_two_pow_sub_one_eq_mod]

theorem and32_high {a : Nat} (ha : a < 2 ^ 32) :
    iand (BitVec.ofNat 32 a) (BitVec.ofNat 32 4294967292) =
      BitVec.ofNat 32 (4 * (a / 4)) := by
  unfold iand
  rw [← BitVec.ofNat_and]
  congr 1
  have hd : (a &&& 4294967292) / 4 = a / 4 := by
    change (a &&& 4294967292) / 2 ^ 2 = _
    rw [Nat.and_div_two_pow]
    change a / 4 &&& (2 ^ 30 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hm : (a &&& 4294967292) % 4 = 0 := by
    change (a &&& 4294967292) % 2 ^ 2 = 0
    rw [Nat.and_mod_two_pow]; simp
  omega

theorem mem_read_one (m : MemInst) (p : Nat) : m.read p 1 = (m.byte p).toNat := by
  simp [MemInst.read]

theorem byte32_toNat (m : MemInst) (p : Nat) :
    (BitVec.ofNat 32 (m.byte p).toNat).toNat = (m.byte p).toNat :=
  ofNat32_toNat (by have := (m.byte p).toNat_lt; omega)

theorem write_size (m : MemInst) (p n v : Nat) : (m.write p n v).size = m.size := rfl

theorem setMem_get {s : Store} {ma : Nat} {m : MemInst} (h : s.mems[ma]? = some m)
    (m' : MemInst) : (s.setMem ma m').mems[ma]? = some m' := by
  exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp h).1

theorem setMem_setMem (s : Store) (ma : Nat) (m m' : MemInst) :
    (s.setMem ma m).setMem ma m' = s.setMem ma m' := by
  simp [Store.setMem, List.set_set]

theorem setMem_self {s : Store} {ma : Nat} {m : MemInst} (h : s.mems[ma]? = some m) :
    s.setMem ma m = s := by
  obtain ⟨hi, hm⟩ := List.getElem?_eq_some_iff.mp h
  rw [← hm]
  simp only [Store.setMem, List.set_getElem_self hi]

theorem setMem_funcs (s : Store) (ma : Nat) (m : MemInst) : (s.setMem ma m).funcs = s.funcs := rfl

theorem eval_decide_true {p : Prop} [Decidable p] (h : p) : decide p = true := by simp [h]

theorem eval_decide_false {p : Prop} [Decidable p] (h : ¬ p) : decide p = false := by simp [h]

attribute [block_simp] eval_decide_true eval_decide_false ofNat32_toNat ofNat32_eq_zero add32
  ltU32 ne32 eqz32 and32_low and32_high
  not_true_eq_false
  mem_read_one byte32_toNat write_size setMem_get setMem_setMem setMem_funcs
  List.length_set List.set_set List.reverse_reverse FVA.Wasm.Num.bool
  seq_vals seqUnique_vals seqAccess_vals vals Val.intBits
  Nat.add_zero Nat.zero_add Nat.add_sub_cancel

@[block_simp] theorem add32_m1 {a : Nat} (h : 1 ≤ a) :
    iadd (BitVec.ofNat 32 a) (BitVec.ofNat 32 4294967295) = BitVec.ofNat 32 (a - 1) := by
  simpa only [Nat.reducePow, Nat.reduceSub] using (add32_neg h (by decide : 1 ≤ 2 ^ 32))

@[block_simp] theorem add32_m4 {a : Nat} (h : 4 ≤ a) :
    iadd (BitVec.ofNat 32 a) (BitVec.ofNat 32 4294967292) = BitVec.ofNat 32 (a - 4) := by
  simpa only [Nat.reducePow, Nat.reduceSub] using (add32_neg h (by decide : 4 ≤ 2 ^ 32))

@[block_simp] theorem ofNat32_add_m1 {a : Nat} (h : 1 ≤ a) :
    BitVec.ofNat 32 (a + 4294967295) = BitVec.ofNat 32 (a - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have he : a + 4294967295 = (a - 1) + 2 ^ 32 := by omega
  rw [he, Nat.add_mod_right]

@[block_simp] theorem instrAccess_storePacked (s : Store) (f : Frame) (w : Width) (p : PackSize)
    (m : MemArg) (v : Val) (i : BitVec 32) (vs : List Val) :
    instrAccess s f (.storePacked w p m) (v :: .i32 i :: vs) =
      match v.intBits w with
      | some _ => rangeAccess s f true (i.toNat + m.offset) (p.bits / 8)
      | none => none := by rw [instrAccess]; rfl

@[block_simp] theorem instrAccess_store (s : Store) (f : Frame) (t : NumType)
    (m : MemArg) (v : Val) (i : BitVec 32) (vs : List Val) :
    instrAccess s f (.store t m) (v :: .i32 i :: vs) =
      match v.numBits t with
      | some _ => rangeAccess s f true (i.toNat + m.offset) t.bytes
      | none => none := by rw [instrAccess]; rfl

@[block_simp 2000] theorem iadd_mask1 (x : BitVec 32) :
    iadd x (BitVec.ofNat 32 4294967295) = x - BitVec.ofNat 32 1 := by
  have hc : BitVec.ofNat 32 4294967295 = -(BitVec.ofNat 32 1) := by decide
  rw [iadd_eq, hc, ← BitVec.sub_eq_add_neg]

@[block_simp 2000] theorem iadd_mask4 (x : BitVec 32) :
    iadd x (BitVec.ofNat 32 4294967292) = x - BitVec.ofNat 32 4 := by
  have hc : BitVec.ofNat 32 4294967292 = -(BitVec.ofNat 32 4) := by decide
  rw [iadd_eq, hc, ← BitVec.sub_eq_add_neg]

@[block_simp] theorem ofNat32_sub {a b : Nat} (hb : b < 2 ^ 32) (hab : b ≤ a) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) :=
  BitVec.ofNat_sub_ofNat_of_le a b hb hab

theorem base_sub (a j k : Nat) (hk : k < 2 ^ 32) (hj : k ≤ a + j) :
    iadd (BitVec.ofNat 32 a - BitVec.ofNat 32 k) (BitVec.ofNat 32 j) =
      BitVec.ofNat 32 (a + j - k) := by
  rw [iadd_eq, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (-(BitVec.ofNat 32 k)),
    ← BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.sub_eq_add_neg, ofNat32_sub hk hj]

end FVA.Wasm.Exec.Ref
