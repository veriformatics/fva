import FVATest.Subjects.EdgerCpm.ExistenceMem
import FVA.Proof.Lib.Walk

namespace Subjects.EdgerCpm.Existence

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem steps_append {H : HostSem} {c c' : Config} (h : Steps H c c')
    (rest : List AInstr) :
    Steps H { c with instrs := c.instrs ++ rest } { c' with instrs := c'.instrs ++ rest } := by
  induction h with
  | refl => exact .refl
  | tail h hs ih =>
    exact ih.tail (by
      simpa only [vals, List.map_nil, List.nil_append] using
        (Step.seq (vs := []) (rest := rest) hs))

theorem fill_zero (m : MemInst) (p : Nat) (f : Nat → UInt8) : m.fill p 0 f = m := by
  have h : (fun a => if p ≤ a ∧ a < p + 0 then f (a - p) else m.byte a) = m.byte := by
    funext a
    simp only [Nat.add_zero, ite_eq_right (show ¬ (p ≤ a ∧ a < p) by omega)]
  unfold MemInst.fill
  rw [h]

theorem fill_succ (m : MemInst) (d n : Nat) (f : Nat → UInt8) :
    (m.write d 1 (f 0).toNat).fill (d + 1) n (fun i => f (i + 1)) =
      m.fill d (n + 1) f := by
  unfold MemInst.fill MemInst.write
  congr 1
  funext a
  by_cases hlo : a < d
  · simp only [ite_eq_right (show ¬ (d + 1 ≤ a ∧ a < d + 1 + n) by omega),
      ite_eq_right (show ¬ (d ≤ a ∧ a < d + 1) by omega),
      ite_eq_right (show ¬ (d ≤ a ∧ a < d + (n + 1)) by omega)]
  · by_cases heq : a = d
    · subst a
      simp
    · by_cases hhi : a < d + n + 1
      · simp only [ite_eq_left (show d + 1 ≤ a ∧ a < d + 1 + n by omega),
          ite_eq_left (show d ≤ a ∧ a < d + (n + 1) by omega)]
        congr 1
        omega
      · simp only [ite_eq_right (show ¬ (d + 1 ≤ a ∧ a < d + 1 + n) by omega),
          ite_eq_right (show ¬ (d ≤ a ∧ a < d + 1) by omega),
          ite_eq_right (show ¬ (d ≤ a ∧ a < d + (n + 1)) by omega)]

theorem setMem_same {s : Store} {m : MemInst} (hm : s.mems[0]? = some m) :
    s.setMem 0 m = s := by
  rcases List.getElem?_eq_some_iff.mp hm with ⟨hi, he⟩
  simp only [Store.setMem, ← he, List.set_getElem_self]

def initInstrs (d q n x : Nat) : List AInstr :=
  [vi32 d, vi32 q, vi32 n, .plain (.memoryInit x)]

theorem memory_init {H : HostSem} {f : Frame} {x da : Nat} {di : DataInst}
    (hmap : f.inst.mems[0]? = some 0) (hda : f.inst.datas[x]? = some da)
    (n : Nat) : ∀ {s : Store} {m : MemInst} {d q : Nat},
      s.mems[0]? = some m → s.datas[da]? = some di →
      q + n ≤ di.data.length → d + n ≤ m.size →
      d + n < 2 ^ 32 → q + n < 2 ^ 32 →
      Steps H ⟨s, f, initInstrs d q n x⟩
        ⟨s.setMem 0 (m.fill d n (fun i => di.data[q + i]!)), f, []⟩ := by
  intro s m d q hm hdi hq hd hd32 hq32
  induction n generalizing s m d q with
  | zero =>
    simp only [Nat.add_zero] at hq hd hd32 hq32
    have hd' : (BitVec.ofNat 32 d).toNat = d := by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd32]
    have hq' : (BitVec.ofNat 32 q).toNat = q := by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq32]
    have hs := Step.memoryInitZero (H := H) (d := .ofNat 32 d) (s' := .ofNat 32 q)
      hmap hda hm hdi (by simpa only [hq'] using hq) (by simpa only [hd'] using hd)
    have hz : (Val.i32 (BitVec.ofNat 32 0)).instr = (Val.i32 0).instr := rfl
    simpa only [initInstrs, vi32, hz, fill_zero, setMem_same hm] using
      Relation.ReflTransGen.single hs
  | succ n ih =>
    have hdlt : d < 2 ^ 32 := by omega
    have hqlt : q < 2 ^ 32 := by omega
    have hnlt : n + 1 < 2 ^ 32 := by omega
    have hd' : (BitVec.ofNat 32 d).toNat = d := by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]
    have hq' : (BitVec.ofNat 32 q).toNat = q := by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqlt]
    have hn' : (BitVec.ofNat 32 (n + 1)).toNat = n + 1 := by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnlt]
    have hidx : q < di.data.length := by omega
    let b := di.data[q]
    have hb : di.data[q]? = some b := List.getElem?_eq_getElem hidx
    have hb32 : b.toNat < 2 ^ 32 := by have := b.toNat_lt; omega
    have hb' : (BitVec.ofNat 32 b.toNat).toNat = b.toNat := by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb32]
    let rest := initInstrs (d + 1) (q + 1) n x
    have hs₁ : Step H ⟨s, f, initInstrs d q (n + 1) x⟩
        ⟨s, f, [vi32 d, vi32 b.toNat, .plain (.storePacked .w32 .p8 ⟨0, 0⟩)] ++ rest⟩ := by
      have h := Step.memoryInit (H := H) (d := .ofNat 32 d) (s' := .ofNat 32 q)
        (n := .ofNat 32 (n + 1)) hmap hda hm hdi
        (by rw [hn']; omega) (by simpa only [hq', hn'] using hq)
        (by simpa only [hd', hn'] using hd) (by simpa only [hq'] using hb)
      simpa only [initInstrs, rest, vi32, hd', hq', hn', Nat.add_sub_cancel,
        List.cons_append, List.nil_append] using h
    have hs₂ : Step H ⟨s, f, [vi32 d, vi32 b.toNat,
        .plain (.storePacked .w32 .p8 ⟨0, 0⟩)]⟩
        ⟨s.setMem 0 (m.write d 1 b.toNat), f, []⟩ := by
      have h := Step.storePacked (H := H) (w := .w32) (p := .p8) (m := ⟨0, 0⟩)
        (i := .ofNat 32 d) (v := .i32 (.ofNat 32 b.toNat)) (c := b.toNat)
        hmap hm (by simp only [Val.intBits, hb']) (by
          simpa only [hd', PackSize.bits, Nat.reduceDiv, Nat.add_zero] using
            (show d + 1 ≤ m.size by omega))
      simpa only [vi32, hd', PackSize.bits, Nat.reduceDiv, Nat.add_zero] using h
    have hi := ih (s := s.setMem 0 (m.write d 1 b.toNat))
      (m := m.write d 1 b.toNat) (d := d + 1) (q := q + 1)
      (setMem_zero hm _) hdi (by omega) (by rw [MemInst.write_size]; omega)
      (by omega) (by omega)
    have he : (s.setMem 0 (m.write d 1 b.toNat)).setMem 0
        ((m.write d 1 b.toNat).fill (d + 1) n (fun i => di.data[q + 1 + i]!)) =
        s.setMem 0 (m.fill d (n + 1) (fun i => di.data[q + i]!)) := by
      have hbget : di.data[q + 0]! = b := by
        simp only [Nat.add_zero, List.getElem!_eq_getElem?_getD, hb, Option.getD_some]
      have hfun : (fun i => di.data[q + 1 + i]!) = (fun i => di.data[q + (i + 1)]!) := by
        funext i
        congr 1
        omega
      rw [hfun, ← hbget, fill_succ m d n (fun i => di.data[q + i]!)]
      simp only [Store.setMem, List.set_set]
    have hs₂' := steps_append (Relation.ReflTransGen.single hs₂) rest
    have hfull := (Relation.ReflTransGen.single hs₁).trans (hs₂'.trans hi)
    simpa only [he] using hfull

end Subjects.EdgerCpm.Existence
