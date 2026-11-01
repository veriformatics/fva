import FVATest.Subjects.Lz4C.Eval.SegCommon
import FVATest.Subjects.Lz4C.Eval.ShortFacts
import FVATest.Subjects.Lz4C.Loop

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false

def dSmall : List Instr :=
  [.localGet 18, .iconst .w32 7, .irelop .w32 (.gt .u), .brIf 0,
    .localGet 17, .iconst .w32 0, .store .i32 ⟨0, 0⟩,
    .localGet 17, .localGet 2, .loadPacked .w32 .p8 .u ⟨0, 0⟩, .storePacked .w32 .p8 ⟨0, 0⟩,
    .localGet 17, .localGet 2, .loadPacked .w32 .p8 .u ⟨0, 1⟩, .storePacked .w32 .p8 ⟨0, 1⟩,
    .localGet 17, .localGet 2, .loadPacked .w32 .p8 .u ⟨0, 2⟩, .storePacked .w32 .p8 ⟨0, 2⟩,
    .localGet 17, .localGet 2, .loadPacked .w32 .p8 .u ⟨0, 3⟩, .storePacked .w32 .p8 ⟨0, 3⟩,
    .localGet 17, .iconst .w32 4, .ibinop .w32 .add, .localGet 2, .localGet 18,
    .iconst .w32 2, .ibinop .w32 .shl, .localTee 18, .load .i32 ⟨2, 65536⟩,
    .ibinop .w32 .add, .localTee 2, .iconst .w32 4, .call 3, .drop,
    .localGet 2, .localGet 18, .load .i32 ⟨2, 65568⟩, .ibinop .w32 .sub, .localSet 2, .br 1]

def dLarge : List Instr :=
  [.localGet 17, .localGet 2, .iconst .w32 8, .call 3, .drop,
    .localGet 2, .iconst .w32 8, .ibinop .w32 .add, .localSet 2]

def dPrologue : Instr := .block .empty (.block .empty dSmall :: dLarge)

def dByteBody : List Instr :=
  [.localGet 18, .localGet 2, .loadPacked .w32 .p8 .u ⟨0, 0⟩, .storePacked .w32 .p8 ⟨0, 0⟩,
    .localGet 2, .iconst .w32 1, .ibinop .w32 .add, .localSet 2,
    .localGet 18, .iconst .w32 1, .ibinop .w32 .add, .localTee 18, .localGet 3,
    .irelop .w32 (.lt .u), .brIf 0, .br 2]

def dByteLoop : Instr := .loop .empty dByteBody

def dNearSetup : List Instr :=
  [.localGet 18, .localGet 10, .irelop .w32 (.ge .u), .brIf 0,
    .localGet 2, .localSet 17, .localGet 18, .localSet 15, wcLoop 15 17 10 [],
    .localGet 2, .localGet 10, .localGet 18, .ibinop .w32 .sub, .ibinop .w32 .add,
    .localSet 2, .localGet 10, .localSet 18]

def dNear : List Instr :=
  [.localGet 3, .localGet 13, .irelop .w32 (.le .u), .brIf 0,
    .localGet 3, .localGet 9, .irelop .w32 (.gt .u), .brIf 4, .block .empty dNearSetup,
    .localGet 18, .localGet 3, .irelop .w32 (.ge .u), .brIf 1, dByteLoop]

noncomputable def dBody : List Instr :=
  [.localGet 2, .localGet 1, .irelop .w32 (.lt .u), .brIf 3,
    .localGet 17, .localGet 15, .ibinop .w32 .add, .iconst .w32 4, .ibinop .w32 .add,
    .localSet 3, dPrologue, .localGet 17, .iconst .w32 8, .ibinop .w32 .add, .localSet 18,
    .block .empty dNear, .localGet 18, .localGet 2, .iconst .w32 8, .call 3, .drop,
    .localGet 15, .iconst .w32 13, .irelop .w32 (.lt .u), .brIf 0,
    .localGet 2, .iconst .w32 8, .ibinop .w32 .add, .localSet 2,
    .localGet 17, .iconst .w32 16, .ibinop .w32 .add, .localSet 17, matchLoop]

theorem d_code : body5.drop 5 = dBody := by kernel_rfl

noncomputable def dAfterPrologue : List Instr := body5.drop 16
noncomputable def dAfterNear : List Instr := body5.drop 21
noncomputable def dAfterFarCopy : List Instr := body5.drop 26

theorem d_after_prologue : dAfterPrologue =
    [.localGet 17, .iconst .w32 8, .ibinop .w32 .add, .localSet 18, .block .empty dNear] ++
      dAfterNear := by kernel_rfl

theorem d_after_near : dAfterNear =
    [.localGet 18, .localGet 2, .iconst .w32 8, .call 3, .drop] ++ dAfterFarCopy := by kernel_rfl

theorem d_after_far_copy : dAfterFarCopy =
    [.localGet 15, .iconst .w32 13, .irelop .w32 (.lt .u), .brIf 0,
      .localGet 2, .iconst .w32 8, .ibinop .w32 .add, .localSet 2,
      .localGet 17, .iconst .w32 16, .ibinop .w32 .add, .localSet 17, matchLoop] := by kernel_rfl

noncomputable def dOuter (es : List AInstr) : List AInstr :=
  [.label 0 [] (.label 0 [] (.label 0 [] (.label 0 [mainLoop] es :: (body4.drop 1).map .plain) ::
    (body3.drop 1).map .plain) :: (body2.drop 1).map .plain)] ++ (body1.drop 54).map .plain

def dLs (src dst n cap cpy j m o' : Nat) (mp : BitVec 32) (v16 v18 : Val) : List Val :=
  [vI src, vI dst, .i32 mp, vI cpy, vI j, vI (dst + cap), vI (dst + cap - 32),
    vI (src + n), vI (src + n - 16), vI (dst + cap - 5), vI (dst + cap - 7),
    vI (src + n - 4), vI (src + n - 8), vI (dst + cap - 12), vI (src + n - 15),
    vI m, v16, vI o', v18]

theorem d_const (src dst n cap cpy j m o' : Nat) (mp : BitVec 32) (v16 v18 : Val) :
    ConstLocals (dLs src dst n cap cpy j m o' mp v16 v18) src dst n cap := by
  simp [ConstLocals, dLs]

def dDelta (off : Nat) : Nat := [0, 1, 2, 2, 4, 3, 2, 1].getD off 0

theorem d_table_bounds {off : Nat} (h : off < 8) :
    inc32[off]! ≤ off ∧ dDelta off ≤ off := by
  interval_cases off <;> decide

theorem d_sub_mask1 (p : Nat) : BitVec.ofNat 32 p - BitVec.ofNat 32 4294967295 =
    BitVec.ofNat 32 (p + 1) := by
  rw [BitVec.sub_eq_add_neg, show -(BitVec.ofNat 32 4294967295) = BitVec.ofNat 32 1 by decide,
    BitVec.ofNat_add_ofNat]

theorem d_sub_mask4 (p : Nat) : BitVec.ofNat 32 p - BitVec.ofNat 32 4294967292 =
    BitVec.ofNat 32 (p + 4) := by
  rw [BitVec.sub_eq_add_neg, show -(BitVec.ofNat 32 4294967292) = BitVec.ofNat 32 4 by decide,
    BitVec.ofNat_add_ofNat]

theorem d_next (p off : Nat) (h : off < 8) :
    BitVec.ofNat 32 (p + inc32[off]!) - BitVec.ofNat 32 dec64[off]! =
      BitVec.ofNat 32 (p + dDelta off) := by
  interval_cases off <;>
    simp (disch := omega) [inc32, dec64, dDelta, d_sub_mask1, d_sub_mask4,
      BitVec.ofNat_sub_ofNat_of_le, Nat.add_sub_assoc, Nat.add_assoc]

theorem d_tables_zero {mem : MemInst} (h : TablesOK mem) {d : Nat} (hd : 131072 ≤ d) :
    TablesOK (mem.write d 4 0) :=
  h.of_low (fun a ha => write_low _ _ _ _ _ (by omega))

theorem d_tables_copy {mem : MemInst} (h : TablesOK mem) {d s k : Nat} (hd : 131072 ≤ d) :
    TablesOK (fwdCopy mem d s k) :=
  h.of_low (fun a ha => fwdCopy_outside _ _ _ _ _ (.inl (by omega)))

/-- The decoder's match copies read the destination buffer, never its source buffer. -/
theorem d_copy (H : HostSem) (C : Context) (st : Store) (inst : ModuleInst) (ls : List Val)
    (a ma : Nat) (mem : MemInst) (src dst n cap d s k : Nat) (rest : List AInstr)
    (hcall : inst.funcs[3]? = some a)
    (hfun : st.funcs[a]? = some (.wasm copyType inst Lifted.func3))
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hend : dst + cap ≤ mem.size) (hsize : mem.size < 2 ^ 32)
    (hr : dst ≤ s ∧ s + k ≤ dst + cap) (hw : dst ≤ d ∧ d + k ≤ dst + cap) :
    Until H (Within (ReadSet ma src n dst cap) (Span ma dst cap))
      (fun c => c = C.fill ⟨st.setMem ma (fwdCopy mem d s k), ⟨ls, inst⟩, vals [vI d] ++ rest⟩)
      (C.fill ⟨st, ⟨ls, inst⟩, vals [vI d, vI s, vI k] ++ [.plain (.call 3)] ++ rest⟩) := by
  apply (short_copy H C st inst ls a ma mem src dst n cap d s k rest hcall hfun hm hmem
    (by omega) (by omega) hsize (.inr hr) hw).mono
  · intro c hc
    refine ⟨fun m x hx => ?_, hc.2⟩
    obtain ⟨hm', hspan⟩ := hc.1 m x hx
    exact ⟨hm', .inr hspan⟩
  · exact fun _ hx => hx

/-- The model's overloaded literal does not match simp's `ofNat`-add pattern. -/
theorem d_add8 (p : Nat) : BitVec.ofNat 32 p + 8 = BitVec.ofNat 32 (p + 8) :=
  BitVec.ofNat_add_ofNat p 8

theorem d_prologue_ptr (mem : MemInst) (dst o' off : Nat) (ht : TablesOK mem)
    (hmatch : dst + off ≤ o') (ho : o' < 2 ^ 32) :
    ∃ p, (prologue mem o' off).2 = BitVec.ofNat 32 p ∧ dst ≤ p ∧ p ≤ o' := by
  have hoff : off ≤ o' := by omega
  have hM := ofNat32_sub (a := o') (b := off) (by omega) hoff
  by_cases hbig : 7 < off
  · refine ⟨o' - off + 8, ?_, by omega, by omega⟩
    simp only [prologue, hbig, ite_true, hM, d_add8]
  · have hsmall : off < 8 := by omega
    have hb := d_table_bounds hsmall
    have hinc := (ht off hsmall).1
    have hdec := (ht off hsmall).2
    refine ⟨o' - off + dDelta off, ?_, by omega, by omega⟩
    simp only [prologue, hbig, ite_false, hM, hinc, hdec, BitVec.ofNat_add_ofNat,
      d_next _ _ hsmall]

end Subjects.Lz4C.Eval
