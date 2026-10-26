import FVATest.Subjects.EdgerCpm.BodyCode
import FVATest.Subjects.EdgerCpm.BodyFloat
import FVATest.Subjects.EdgerCpm.BodyCells

namespace Subjects.EdgerCpm.Body

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

theorem column_step (C : Context) (H : HostSem) (Q : Outcome → Prop) (s : Store)
    (inst : ModuleInst) (tail : List AInstr) (x : Input) (l : Layout) (t b : BitVec 32)
    (r j : Nat) (mem : MemInst) (count lib : BitVec 64)
    (hj : j < x.m) (hm32 : x.m < 2 ^ 32) (hn8 : 8 * x.n < 2 ^ 32)
    (hp32 : l.cell x r j < 2 ^ 32) (hb32 : b.toNat + 8 * j < 2 ^ 32)
    (hm : inst.mems[0]? = some 0) (hmem : s.mems[0]? = some mem)
    (hp : l.cell x r j + 8 ≤ mem.size) (hb : b.toNat + 8 * j + 8 ≤ mem.size)
    (hcount : mem.read (l.cell x r j) 8 = count.toNat)
    (hlib : mem.read (b.toNat + 8 * j) 8 = lib.toNat)
    (hk : ∀ out, CpmElem count lib out →
      Must H Q (C.fill ⟨put s mem (l.cell x r j) 8 out.toNat,
        mainFrame x l inst t r (j + 1) (.ofNat 32 (l.cell x r (j + 1))) b,
        columnHead tail⟩)) :
    Must H Q (C.fill ⟨s, mainFrame x l inst t r j (.ofNat 32 (l.cell x r j)) b,
      columnHead tail⟩) := by
  have j32 : j < 2 ^ 32 := lt_trans hj hm32
  have hjnat : (BitVec.ofNat 32 j).toNat = j := Nat.mod_eq_of_lt j32
  have hmnat : (BitVec.ofNat 32 x.m).toNat = x.m := Nat.mod_eq_of_lt hm32
  have hnnat : (BitVec.ofNat 32 x.n).toNat = x.n := Nat.mod_eq_of_lt (by omega)
  have hpnat : (BitVec.ofNat 32 (l.cell x r j)).toNat = l.cell x r j := Nat.mod_eq_of_lt hp32
  have h8jnat : (BitVec.ofNat 32 (8 * j)).toNat = 8 * j := Nat.mod_eq_of_lt (by omega)
  have h8nnat : (BitVec.ofNat 32 (8 * x.n)).toNat = 8 * x.n := Nat.mod_eq_of_lt hn8
  have heq : ieq (.ofNat 32 j) (.ofNat 32 x.m) = 0 := by
    simp [ieq, Num.bool, hmnat, hjnat, show j ≠ x.m by omega]
  have hshj : ishl (.ofNat 32 j) (.ofNat 32 3) = BitVec.ofNat 32 (8 * j) := by
    simp [ishl, hjnat, Nat.mul_comm]
  have hshn : ishl (.ofNat 32 x.n) (.ofNat 32 3) = BitVec.ofNat 32 (8 * x.n) := by
    simp [ishl, hnnat, Nat.mul_comm]
  have hab : iadd b (.ofNat 32 (8 * j)) = BitVec.ofNat 32 (b.toNat + 8 * j) := by
    simp only [iadd, h8jnat]
  have hbptr : (BitVec.ofNat 32 (b.toNat + 8 * j)).toNat = b.toNat + 8 * j :=
    Nat.mod_eq_of_lt hb32
  have hinc : iadd (.ofNat 32 j) (.ofNat 32 1) = BitVec.ofNat 32 (j + 1) := by
    simp only [iadd, hjnat, show (BitVec.ofNat 32 1).toNat = 1 from rfl]
  have hnext : iadd (.ofNat 32 (l.cell x r j)) (.ofNat 32 (8 * x.n)) =
      BitVec.ofNat 32 (l.cell x r (j + 1)) := by
    simp only [iadd, hpnat, h8nnat]
    congr 1
    simp only [Layout.cell, Nat.mul_add, Nat.mul_one]
    omega
  have hbp : ¬ mem.size < l.cell x r j + 8 := by omega
  have hbb : ¬ mem.size < b.toNat + 8 * j + 8 := by omega
  have hmillion : toVal (.plain (.fconst .w64 4696837146684686336)) =
      some (.f64 0x412E848000000000) := rfl
  unfold mainFrame columnHead
  iterate 9 wasm_cstep [columnLoop, rowCode, rowLoop, processCode, outerCode, outerLoop,
    blockCode, loopCode, thenCode, Lifted.func86, List.getD, List.drop_succ_cons,
    List.drop_zero, hm, hmem, heq, hpnat, hbp, hcount, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, Nat.add_zero]
  apply must_mul64_context C count 0x412E848000000000
  · simp [seqFocus, atFocus, NumAt, toVal_instr, toVal_label, toVal_fbinop, hmillion]
  · intro tmp htmp
    simp only [seqPlug, atPlug, wasm_step, vals, hmillion]
    iterate 5 wasm_cstep [hm, hmem, hshj, hab, hbptr, hbb, hlib, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, Nat.add_zero]
    apply must_div64_context C tmp lib
    · simp [seqFocus, atFocus, NumAt, toVal_instr, toVal_label, toVal_fbinop]
    · intro out hout
      simp only [seqPlug, atPlug, wasm_step, vals]
      iterate 10 wasm_cstep [hm, hmem, hpnat, hbp, Val.numBits, Nat.add_zero,
        hinc, hshn, hnext]
      exact hk out ⟨ofBits f64fmt tmp, htmp, hout⟩

theorem column_exit (C : Context) (H : HostSem) (Q : Outcome → Prop) (s : Store)
    (inst : ModuleInst) (tail : List AInstr) (x : Input) (l : Layout) (t b p : BitVec 32)
    (r : Nat) (hr32 : r < 2 ^ 32)
    (hk : Must H Q (C.fill ⟨s, mainFrame x l inst t (r + 1) x.m p b,
      .plain rowLoop :: tail⟩)) :
    Must H Q (C.fill ⟨s, mainFrame x l inst t r x.m p b, columnHead tail⟩) := by
  have heq : ieq (BitVec.ofNat 32 x.m) (.ofNat 32 x.m) = 1 := by simp [ieq, Num.bool]
  have hone : (1 : BitVec 32) ≠ 0 := by decide
  have hrnat : (BitVec.ofNat 32 r).toNat = r := Nat.mod_eq_of_lt hr32
  have hinc : iadd (.ofNat 32 r) (.ofNat 32 1) = BitVec.ofNat 32 (r + 1) := by
    simp only [iadd, hrnat, show (BitVec.ofNat 32 1).toNat = 1 from rfl]
  unfold columnHead mainFrame
  iterate 10 wasm_cstep [columnLoop, rowCode, rowLoop, processCode, outerCode, outerLoop,
    blockCode, loopCode, thenCode, Lifted.func86, List.getD, List.drop_succ_cons,
    List.drop_zero, heq, hone, hinc]
  exact hk

theorem column_loop (C : Context) (H : HostSem) (Q : Outcome → Prop) (inst : ModuleInst)
    (tail : List AInstr) (x : Input) (l : Layout) (t b : BitVec 32) (r : Nat)
    (s₀ : Store) (hr : r < x.n) (hm32 : x.m < 2 ^ 32) (hn8 : 8 * x.n < 2 ^ 32)
    (hc32 : l.c + 8 * x.n * x.m ≤ 2 ^ 32) (hb32 : b.toNat + 8 * x.m ≤ 2 ^ 32)
    (hm : inst.mems[0]? = some 0) (hcopied : Copied s₀ x b x.m)
    (hsep : ∀ a, b.toNat ≤ a → a < b.toNat + 8 * x.m → ¬ l.counts x a)
    (hk : ∀ s, Changed s₀ s (fun a => ¬ l.counts x a) → Cells s x l r x.m →
      Must H Q (C.fill ⟨s, mainFrame x l inst t (r + 1) x.m
        (.ofNat 32 (l.cell x r x.m)) b, .plain rowLoop :: tail⟩)) :
    ∀ k j s, j + k = x.m → Changed s₀ s (fun a => ¬ l.counts x a) → Cells s x l r j →
      Must H Q (C.fill ⟨s, mainFrame x l inst t r j (.ofNat 32 (l.cell x r j)) b,
        columnHead tail⟩) := by
  intro k
  induction k with
  | zero =>
    intro j s hj hchange hcells
    have hj' : j = x.m := by omega
    subst j
    exact column_exit C H Q s inst tail x l t b _ r (by omega) (hk s hchange hcells)
  | succ k ih =>
    intro j s hj hchange hcells
    have hjm : j < x.m := by omega
    obtain ⟨before, mem, hbefore, hmem, hs, hpages, hmax, hbytes⟩ := hchange
    have hchange : Changed s₀ s (fun a => ¬ l.counts x a) :=
      ⟨before, mem, hbefore, hmem, hs, hpages, hmax, hbytes⟩
    have hbuf : Holds s (b.toNat + 8 * j) (le64 (x.libSize j)) := by
      apply holds_same (changed_same hchange) (hcopied j hjm)
      intro a ha hb
      apply hsep a (by omega)
      simp [le64, Binary.leBytes] at hb
      omega
    have hcount := (hcells r hr j hjm).2 (by simp [Done])
    have hp : l.cell x r j + 8 ≤ mem.size := by
      simpa [le64, Binary.leBytes] using holds_size hmem hcount
    have hb : b.toNat + 8 * j + 8 ≤ mem.size := by
      simpa [le64, Binary.leBytes] using holds_size hmem hbuf
    have hcEnd := cell_end (l := l) hr hjm
    apply column_step C H Q s inst tail x l t b r j mem (x.count r j) (x.libSize j)
      hjm hm32 hn8 (by omega) (by omega) hm hmem hp hb (read64 hmem hcount) (read64 hmem hbuf)
    intro out hout
    apply ih (j + 1) (put s mem (l.cell x r j) 8 out.toNat) (by omega)
    · apply changed_put hchange hmem
      intro a hn hz
      exact hn (cell_counts hr hjm hz.1 hz.2)
    · exact cells_put hr hjm hmem hp hcells hout

end Subjects.EdgerCpm.Body
