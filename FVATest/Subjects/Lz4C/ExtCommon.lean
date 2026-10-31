import FVATest.Subjects.Lz4C.Ext
import FVA.Proof.Lib.Arith

/-! Facts both checkpoint-1 routes step with: the loop head, `i32` arithmetic on `ofNat` values,
local updates, one-byte reads (proof support; outside the review surface). -/

namespace Subjects.Lz4C

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

/-- The loop head: the loop's label holding its whole body, frame `f`. -/
noncomputable def head (C : Context) (s : Store) (f : Frame) : Config :=
  (ctx9 C).fill ⟨s, f, [.label 0 [.loop .empty extBody] (extBody.map .plain)]⟩

theorem ofNat_toNat {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n :=
  Nat.mod_eq_of_lt h

theorem iadd_ofNat (a b : Nat) : iadd (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) =
    BitVec.ofNat 32 (a + b) := by
  rw [iadd_eq, BitVec.ofNat_add]

theorem igtU_ofNat {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    igtU (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = bool (decide (b < a)) := by
  simp only [igtU, ofNat_toNat ha, ofNat_toNat hb, gt_iff_lt]

-- the literal `2147483648`, never `2 ^ 31`: simp would rewrite the power inside `decide`, leaving
-- an instance no later lemma matches
theorem iltS_zero {a : Nat} (ha : a < 2 ^ 32) :
    iltS (BitVec.ofNat 32 a) (BitVec.ofNat 32 0) = bool (decide (2147483648 ≤ a)) := by
  simp only [iltS, signed, ofNat_toNat ha, BitVec.toNat_ofNat, Nat.zero_mod]
  congr 1
  simp only [decide_eq_decide]
  split <;> omega

theorem ieq_ofNat {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    ieq (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = bool (a == b) := by
  simp only [ieq, ofNat_toNat ha, ofNat_toNat hb]

theorem bool_true : bool true = 1 := rfl
theorem bool_false : bool false = 0 := rfl
theorem one_ne : decide ((1 : BitVec 32) = 0) = false := by decide
theorem zero_eq : decide ((0 : BitVec 32) = 0) = true := by decide

theorem getElem?_set_of_ne {l : List Val} {i k : Nat} {v : Val} (h : k ≠ i) :
    (l.set k v)[i]? = l[i]? := List.getElem?_set_ne h

theorem read_one (mem : MemInst) (a : Nat) : mem.read a 1 = (mem.byte a).toNat := by
  simp [MemInst.read]

end Subjects.Lz4C
