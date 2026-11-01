import FVATest.Subjects.Lz4C.Eval.Code

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

@[block_simp] theorem fwdCopy_size (mem : MemInst) (d s n : Nat) :
    (fwdCopy mem d s n).size = mem.size := by
  induction n generalizing mem d s with
  | zero => rfl
  | succ n ih => simp only [fwdCopy, ih, write_size]

theorem fwdCopy_add (mem : MemInst) (d s a b : Nat) :
    fwdCopy mem d s (a + b) = fwdCopy (fwdCopy mem d s a) (d + a) (s + a) b := by
  induction a generalizing mem d s with
  | zero => simp only [Nat.zero_add, Nat.add_zero, fwdCopy]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, fwdCopy, ih]
    simp only [fwdCopy, Nat.add_assoc, Nat.add_comm 1 a]

@[block_simp] theorem fwdCopy_one (mem : MemInst) (d s : Nat) :
    fwdCopy mem d s 1 = mem.write d 1 (mem.byte s).toNat := rfl

@[block_simp] theorem four_writes (mem : MemInst) (d s : Nat) :
    let m1 := mem.write d 1 (mem.byte s).toNat
    let m2 := m1.write (d + 1) 1 (m1.byte (s + 1)).toNat
    let m3 := m2.write (d + 2) 1 (m2.byte (s + 2)).toNat
    m3.write (d + 3) 1 (m3.byte (s + 3)).toNat = fwdCopy mem d s 4 := by
  simp only [fwdCopy, Nat.add_assoc, Nat.reduceAdd]

end Subjects.Lz4C.Eval
