import FVATest.Subjects.Lz4C.Eval.S1

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

set_option linter.unusedSimpArgs false

/-- Descending copy, preserving each read after earlier (higher-address) writes. -/
def backCopy (mem : MemInst) (d s : Nat) : Nat → MemInst
  | 0 => mem
  | n + 1 => backCopy (mem.write (d + n) 1 (mem.byte (s + n)).toNat) d s n

@[block_simp] theorem backCopy_size (mem : MemInst) (d s n : Nat) :
    (backCopy mem d s n).size = mem.size := by
  induction n generalizing mem with
  | zero => rfl
  | succ n ih => simp only [backCopy, ih, write_size]

theorem backCopy_add (mem : MemInst) (d s a b : Nat) :
    backCopy mem d s (a + b) = backCopy (backCopy mem (d + b) (s + b) a) d s b := by
  induction a generalizing mem with
  | zero => simp only [Nat.zero_add, backCopy]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, backCopy, ih]
    simp only [backCopy, Nat.add_assoc, Nat.add_comm b a]

theorem write_byte_one (mem : MemInst) (d v a : Nat) :
    (mem.write d 1 v).byte a = if a = d then UInt8.ofNat v else mem.byte a := by
  by_cases h : a = d
  · subst a; simp [MemInst.write]
  · have hn : ¬ (d ≤ a ∧ a < d + 1) := by omega
    simp only [MemInst.write, hn, ite_false, h]

theorem move_fwd_step (mem : MemInst) (d s n : Nat) (hds : d ≤ s) :
    move (mem.write d 1 (mem.byte s).toNat) (d + 1) (s + 1) n = move mem d s (n + 1) := by
  cases mem
  simp only [move, MemInst.write]
  congr 1
  funext a
  by_cases he : a = d
  · subst a
    simp only [true_and, and_true, false_and, and_false, Nat.lt_irrefl,
      show ¬ (d + 1 ≤ d ∧ d < d + 1 + n) by omega, ite_false,
      show d ≤ d ∧ d < d + 1 by omega, ite_true, Nat.sub_self, Nat.pow_zero, Nat.div_one,
      UInt8.ofNat_toNat, show d ≤ d ∧ d < d + (n + 1) by omega, Nat.add_zero]
  · by_cases hr : d ≤ a ∧ a < d + (n + 1)
    · have hl : d + 1 ≤ a ∧ a < d + 1 + n := by omega
      have hp : ¬ (d ≤ s + 1 + (a - (d + 1)) ∧ s + 1 + (a - (d + 1)) < d + 1) := by omega
      simp only [hr, hl, hp, true_and, and_true, false_and, and_false, ite_true, ite_false]
      rw [show s + 1 + (a - (d + 1)) = s + (a - d) by omega]
    · have hl : ¬ (d + 1 ≤ a ∧ a < d + 1 + n) := by omega
      have hp : ¬ (d ≤ a ∧ a < d + 1) := by omega
      simp only [hr, hl, hp, ite_false]

theorem move_back_step (mem : MemInst) (d s n : Nat) (hsd : s ≤ d) :
    move (mem.write (d + n) 1 (mem.byte (s + n)).toNat) d s n = move mem d s (n + 1) := by
  cases mem
  simp only [move, MemInst.write]
  congr 1
  funext a
  by_cases he : a = d + n
  · subst a
    simp only [true_and, and_true, false_and, and_false, Nat.lt_irrefl,
      show ¬ (d ≤ d + n ∧ d + n < d + n) by omega, ite_false,
      show d + n ≤ d + n ∧ d + n < d + n + 1 by omega, ite_true, Nat.sub_self,
      Nat.pow_zero, Nat.div_one, UInt8.ofNat_toNat,
      show d ≤ d + n ∧ d + n < d + (n + 1) by omega,
      show d + n - d = n by omega]
  · by_cases hr : d ≤ a ∧ a < d + n
    · have hbig : d ≤ a ∧ a < d + (n + 1) := by omega
      have hp : ¬ (d + n ≤ s + (a - d) ∧ s + (a - d) < d + n + 1) := by omega
      simp only [hr, hbig, hp, true_and, and_true, false_and, and_false, ite_true, ite_false]
    · have hbig : ¬ (d ≤ a ∧ a < d + (n + 1)) := by omega
      have hp : ¬ (d + n ≤ a ∧ a < d + n + 1) := by omega
      simp only [hr, hbig, hp, ite_false]

theorem move_zero (mem : MemInst) (d s : Nat) : move mem d s 0 = mem := by
  have hz : ∀ a, ¬ (d ≤ a ∧ a < d) := by intro a; omega
  simp only [move, Nat.add_zero, hz, ite_false]

theorem fwdCopy_eq_move (mem : MemInst) (d s n : Nat) (hds : d ≤ s) :
    fwdCopy mem d s n = move mem d s n := by
  induction n generalizing mem d s with
  | zero => rw [move_zero]; rfl
  | succ n ih => rw [fwdCopy, ih _ _ _ (by omega), move_fwd_step _ _ _ _ hds]

theorem backCopy_eq_move (mem : MemInst) (d s n : Nat) (hsd : s ≤ d) :
    backCopy mem d s n = move mem d s n := by
  induction n generalizing mem with
  | zero => rw [move_zero]; rfl
  | succ n ih => rw [backCopy, ih, move_back_step _ _ _ _ hsd]

@[block_simp] theorem four_back_writes (mem : MemInst) (d s : Nat) :
    let m1 := mem.write (d + 3) 1 (mem.byte (s + 3)).toNat
    let m2 := m1.write (d + 2) 1 (m1.byte (s + 2)).toNat
    let m3 := m2.write (d + 1) 1 (m2.byte (s + 1)).toNat
    m3.write d 1 (m3.byte s).toNat = backCopy mem d s 4 := by
  simp only [backCopy, Nat.reduceAdd, Nat.add_zero]

end Subjects.Lz4C.Eval
