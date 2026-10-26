import FVATest.Subjects.EdgerCpm.BodyState

namespace Subjects.EdgerCpm.Body

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

theorem row_call (C : Context) (H : HostSem) (Q : Outcome → Prop) (s : Store)
    (inst : ModuleInst) (tail : List AInstr) (x : Input) (l : Layout)
    (t b oldp oldb : BitVec 32) (r oldj a207 : Nat) (mem : MemInst)
    (hr : r < x.n) (hn32 : x.n < 2 ^ 32) (hm : inst.mems[0]? = some 0)
    (hmem : s.mems[0]? = some mem) (ht : t.toNat + 4 ≤ mem.size)
    (htable : mem.read t.toNat 4 = b.toNat) (hi : inst.funcs[207]? = some a207)
    (hk : Must H Q ((Context.label 0 [rowLoop] tail C).fill
      ⟨s, mainFrame x l inst t r oldj oldp b,
        vals [.i32 (.ofNat 32 l.lib), .i32 (.ofNat 32 r), .i32 b] ++ [.invoke a207] ++
          (rowCode.drop 10).map .plain⟩)) :
    Must H Q (C.fill ⟨s, mainFrame x l inst t r oldj oldp oldb,
      .plain rowLoop :: tail⟩) := by
  have hrnat : (BitVec.ofNat 32 r).toNat = r := Nat.mod_eq_of_lt (lt_trans hr hn32)
  have hnnat : (BitVec.ofNat 32 x.n).toNat = x.n := Nat.mod_eq_of_lt hn32
  have heq : ieq (.ofNat 32 r) (.ofNat 32 x.n) = 0 := by
    simp [ieq, Num.bool, hrnat, hnnat, show r ≠ x.n by omega]
  have hb : ¬ mem.size < t.toNat + 4 := by omega
  unfold mainFrame
  iterate 14 wasm_cstep [rowLoop, processCode, outerCode, outerLoop, blockCode,
    loopCode, thenCode, Lifted.func86, List.getD, hm, hmem, heq, hb, htable, hi,
    BitVec.ofNat_toNat, BitVec.setWidth_eq, Nat.add_zero]
  exact hk

theorem row_column (C : Context) (H : HostSem) (Q : Outcome → Prop) (s : Store)
    (inst : ModuleInst) (tail : List AInstr) (x : Input) (l : Layout)
    (t b oldp : BitVec 32) (r oldj : Nat) (hr32 : r < 2 ^ 32)
    (hp32 : l.cell x r 0 < 2 ^ 32)
    (hk : Must H Q (C.fill ⟨s, mainFrame x l inst t r 0 (.ofNat 32 (l.cell x r 0)) b,
      columnHead tail⟩)) :
    Must H Q ((Context.label 0 [rowLoop] tail C).fill
      ⟨s, mainFrame x l inst t r oldj oldp b, (rowCode.drop 10).map .plain⟩) := by
  have hrnat : (BitVec.ofNat 32 r).toNat = r := Nat.mod_eq_of_lt hr32
  have hcnat : (BitVec.ofNat 32 l.c).toNat = l.c := Nat.mod_eq_of_lt (by
    simp only [Layout.cell, Nat.mul_zero, Nat.add_zero] at hp32
    omega)
  have h8nat : (BitVec.ofNat 32 (8 * r)).toNat = 8 * r := Nat.mod_eq_of_lt (by
    simp only [Layout.cell, Nat.mul_zero, Nat.add_zero] at hp32
    omega)
  have hsh : ishl (.ofNat 32 r) (.ofNat 32 3) = BitVec.ofNat 32 (8 * r) := by
    simp [ishl, hrnat, Nat.mul_comm]
  have hadd : iadd (.ofNat 32 l.c) (.ofNat 32 (8 * r)) =
      BitVec.ofNat 32 (l.cell x r 0) := by
    simp only [iadd, hcnat, h8nat, Layout.cell, Nat.mul_zero, Nat.add_zero]
  change Must H Q (C.fill ⟨s, mainFrame x l inst t r oldj oldp b,
    .label 0 [rowLoop] ((rowCode.drop 10).map .plain) :: tail⟩)
  unfold mainFrame
  iterate 6 wasm_cstep [rowCode, rowLoop, processCode, outerCode, outerLoop, blockCode,
    loopCode, thenCode, Lifted.func86, List.getD, List.drop_succ_cons, List.drop_zero,
    hsh, hadd]
  exact hk

theorem row_loop (W : World) (t b : BitVec 32) (C : Context) (tail : List AInstr)
    (Q : Outcome → Prop)
    (hk : ∀ s j p last, LoopState W t b W.x.n s →
      Must W.H Q (C.fill ⟨s, mainFrame W.x W.l W.inst t W.x.n j p last,
        .plain rowLoop :: tail⟩)) :
    ∀ k r s j p last, r + k = W.x.n → LoopState W t b r s →
      Must W.H Q (C.fill ⟨s, mainFrame W.x W.l W.inst t r j p last,
        .plain rowLoop :: tail⟩) := by
  intro k
  induction k with
  | zero =>
    intro r s j p last hr hstate
    have hr' : r = W.x.n := by omega
    subst r
    exact hk s j p last hstate
  | succ k ih =>
    intro r s j p last hr hstate
    have hrn : r < W.x.n := by omega
    obtain ⟨mem, hmem, htable, hbuffer⟩ := hstate.scratch.room
    obtain ⟨hm, a160, a207, a12, a13, hi207, hi12, hi13, hex, f160, f207, f12, f13⟩ :=
      hstate.linked
    apply row_call C W.H Q s W.inst tail W.x W.l t b p last r j a207 mem hrn
      (by have := W.n31; omega) hm hmem htable (read32 hmem hstate.table) hi207
    apply get_row_type2 (Context.label 0 [rowLoop] tail C) W.H Q s W.inst
      (mainFrame W.x W.l W.inst t r j p b) ((rowCode.drop 10).map .plain) W.x W.l
      a207 b (.ofNat 32 r) mem W.domain.2.1 W.m31 W.libBound W.dataBound
      hstate.scratch.bufferBound hm hmem hbuffer
      (by simpa only [row_type] using f207) hstate.library
      (fun a ha => hstate.outside_buffer (Or.inl ha))
    intro s₁ hchange hcopied
    have hstate₁ := hstate.copy hchange
    have hend := cell_end (l := W.l) hrn W.domain.2.1
    have hp32 : W.l.cell W.x r 0 < 2 ^ 32 := by have := W.countsBound; omega
    apply row_column C W.H Q s₁ W.inst tail W.x W.l t b p r j
      (by have := W.n31; omega) hp32
    apply column_loop C W.H Q W.inst tail W.x W.l t b r s₁ hrn
      (by have := W.m31; omega) W.n8 W.countsBound hstate₁.scratch.bufferBound hm hcopied
      (fun a ha hb hc => by
        have hh := hstate₁.outside_buffer (Or.inr hc)
        unfold outsideBuffer at hh
        omega)
      (fun s₂ hchange₂ hcells₂ => ih (r + 1) s₂ W.x.m
        (.ofNat 32 (W.l.cell W.x r W.x.m)) b (by omega) (hstate₁.column hchange₂ hcells₂))
      W.x.m 0 s₁ (by omega)
    · obtain ⟨mem₁, hmem₁, -⟩ := hstate₁.scratch.room
      exact changed_refl hmem₁
    · exact hstate₁.cells

noncomputable def bodyContext : Context :=
  .label 0 [] ((outerCode.drop 4).map .plain)
    (.label 0 [] [] (.label 0 [outerLoop] ((Lifted.func86.body.drop 15).map .plain)
      (.label 0 [] [] (.frame 0 ⟨[], {}⟩ [] .hole))))

theorem row_start (H : HostSem) (Q : Outcome → Prop) (s : Store) (inst : ModuleInst)
    (x : Input) (l : Layout) (t : BitVec 32) (hn0 : 0 < x.n) (hm0 : 0 < x.m)
    (hn31 : x.n < 2 ^ 31) (hm31 : x.m < 2 ^ 31)
    (hk : Must H Q (bodyContext.fill ⟨s, mainFrame x l inst t 0 1 0 0,
      .plain rowLoop :: (processCode.drop 17).map .plain⟩)) :
    Must H Q ⟨s, ⟨[], {}⟩, allocatedHead x l inst t⟩ := by
  have hnnat : (BitVec.ofNat 32 x.n).toNat = x.n := Nat.mod_eq_of_lt (by omega)
  have hmnat : (BitVec.ofNat 32 x.m).toNat = x.m := Nat.mod_eq_of_lt (by omega)
  have hgn : igtS (BitVec.ofNat 32 x.n) (BitVec.ofNat 32 0) = 1 := by
    have hn : x.n < 2147483648 := hn31
    simp [igtS, signed, Num.bool, hnnat, hn, hn0]
  have hgm : igtS (BitVec.ofNat 32 x.m) (BitVec.ofNat 32 0) = 1 := by
    have hm : x.m < 2147483648 := hm31
    simp [igtS, signed, Num.bool, hmnat, hm, hm0]
  have heq : ieq (1 : BitVec 32) (.ofNat 32 1) = 1 := by decide
  have hone : (1 : BitVec 32) ≠ 0 := by decide
  unfold allocatedHead tableFrame prefixFrame
  iterate 17 wasm_step1 [Lifted.func86, List.drop_succ_cons, List.drop_zero, heq, hone,
    hgn, hgm]
  exact hk

end Subjects.EdgerCpm.Body
