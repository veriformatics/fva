import FVA.Proof.Lib.BlockNumeric
import FVATest.Subjects.Lz4C.Eval.SegCommon

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false

def cGuard : List Instr :=
  [.localGet 4, .iconst .w32 1, .ibinop .w32 .add, .localTee 3, .localGet 11,
    .irelop .w32 (.le .u), .brIf 0, .localGet 3, .localSet 4, .br 5]

def cFirst : List Instr :=
  [.localGet 4, .loadPacked .w32 .p8 .u ⟨0, 0⟩, .localTee 15,
    .iconst .w32 255, .irelop .w32 .eq, .brIf 0, .localGet 3, .localSet 4, .br 1]

def cLoopBody : List Instr :=
  [.localGet 3, .iconst .w32 1, .ibinop .w32 .add, .localTee 4, .localGet 11,
    .irelop .w32 (.gt .u), .brIf 4, .localGet 15, .localGet 3,
    .loadPacked .w32 .p8 .u ⟨0, 0⟩, .localTee 16, .ibinop .w32 .add, .localTee 15,
    .iconst .w32 0, .irelop .w32 (.lt .s), .brIf 4, .localGet 4, .localSet 3,
    .localGet 16, .iconst .w32 255, .irelop .w32 .eq, .brIf 0]

def cLoop : Instr := .loop .empty cLoopBody

def cExt : List Instr := [.block .empty cFirst, .iconst .w32 255, .localSet 15, cLoop]

def cTail : List Instr :=
  [.localGet 15, .iconst .w32 15, .ibinop .w32 .add, .localTee 15, .localGet 17,
    .iconst .w32 4294967295, .ibinop .w32 .xor, .irelop .w32 (.gt .u), .brIf 4]

def cSegment : List Instr :=
  [.localGet 15, .iconst .w32 15, .irelop .w32 .ne, .brIf 0,
    .block .empty cGuard, .block .empty cExt] ++ cTail

theorem c_code : body6.drop 1 = cSegment := by kernel_rfl

theorem c_after3 : body3.drop 1 =
    [.localGet 3, .iconst .w32 1, .ibinop .w32 .add, .localSet 4, .br 1] := by kernel_rfl

noncomputable def cWrap (es : List AInstr) : List AInstr :=
  cOuter (.label 0 [] es :: cTail.map .plain)

theorem c_xor {x : Nat} (hx : x < 2 ^ 32) :
    ixor (BitVec.ofNat 32 x) (BitVec.ofNat 32 4294967295) =
      BitVec.ofNat 32 (4294967295 - x) := by
  unfold ixor
  rw [show BitVec.ofNat 32 4294967295 = BitVec.allOnes 32 by decide, BitVec.xor_allOnes]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_not, ofNat32_toNat hx,
    ofNat32_toNat (show 4294967295 - x < 2 ^ 32 by omega), Nat.reducePow, Nat.reduceSub]

/-- Exit the extension block and its overflow guard. -/
theorem c_footer (H : HostSem) (F : Context) (st : Store) (inst : ModuleInst) (ma : Nat)
    (src dst n cap o' off acc j : Nat) (v3 v16 : Val)
    (hn : n ≤ 2097152) (ha : acc ≤ 255 * n) (ho : o' < 2 ^ 31) :
    Until H
      (Within (fun m x => m = ma ∧ (Span ma src n m x ∨ Span ma dst cap m x)) (Span ma dst cap))
      (AtX4 F st inst src dst n cap o' off (15 + acc) j)
      ((ctx1 F).fill ⟨st, ⟨cLocals src dst n cap o' off v3 (vI j) acc v16, inst⟩,
        cOuter (cTail.map .plain)⟩) := by
  have hac : acc + 15 < 2 ^ 31 := by omega
  have hcmp : acc + 15 ≤ 4294967295 - o' := by omega
  have hadd : acc + 15 = 15 + acc := by omega
  wasm_eval 9 [block_simp, cOuter, cTail, cLocals, c_xor, igtU_ofNat, hadd]
  · simp [TraceOK, AccessOK]
  · apply Until.done
    simpa only [BContext.fill, ctx5, ctx4, ctx2, Context.fill, cLocals] using
      c_atX4 F st inst src dst n cap o' off v3 j (15 + acc) v16

theorem c_finish (H : HostSem) (F : Context) (st : Store) (inst : ModuleInst) (ma : Nat)
    (src dst n cap o' off acc j : Nat) (v3 v16 : Val)
    (hn : n ≤ 2097152) (ha : acc ≤ 255 * n) (ho : o' < 2 ^ 31) :
    Until H
      (Within (fun m x => m = ma ∧ (Span ma src n m x ∨ Span ma dst cap m x)) (Span ma dst cap))
      (AtX4 F st inst src dst n cap o' off (15 + acc) j)
      ((ctx1 F).fill ⟨st, ⟨cLocals src dst n cap o' off v3 (vI j) acc v16, inst⟩, cWrap []⟩) := by
  wasm_eval 1 [block_simp, cWrap, cOuter, cLocals]
  · simp [TraceOK, AccessOK]
  · simpa only [BContext.fill, cOuter, cLocals, List.singleton_append] using
      c_footer H F st inst ma src dst n cap o' off acc j v3 v16 hn ha ho

def cResult (F : Context) (st : Store) (inst : ModuleInst) (mem : MemInst)
    (src dst n cap o' off fuel q acc : Nat) (c : Config) : Prop :=
  (∃ a q', extM mem (src + n - 4) fuel q acc = some (a, q') ∧
    AtX4 F st inst src dst n cap o' off (15 + a) q' c) ∨
  (extM mem (src + n - 4) fuel q acc = none ∧ Err F st inst src dst n cap c)

/-- Model fuel bounds remaining reads; each iteration is one evaluator rewrite. -/
theorem c_loop (H : HostSem) (F : Context) (st : Store) (inst : ModuleInst) (ma : Nat)
    (mem : MemInst) (src dst n cap o' off fuel q acc : Nat) (v4 v16 : Val)
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hs : src + n ≤ mem.size) (hsize : mem.size ≤ 2097152) (ho : o' < 2 ^ 31)
    (hlo : src ≤ q) (hhi : q ≤ src + n) (hbudget : src + n - 4 ≤ q + fuel)
    (hacc : acc + 255 * fuel ≤ 255 * n) :
    Until H
      (Within (fun m x => m = ma ∧ (Span ma src n m x ∨ Span ma dst cap m x)) (Span ma dst cap))
      (cResult F st inst mem src dst n cap o' off fuel q acc)
      ((ctx1 F).fill ⟨st, ⟨cLocals src dst n cap o' off (vI q) v4 acc v16, inst⟩,
        cWrap [.plain cLoop]⟩) := by
  have hn : n ≤ 2097152 := by omega
  induction fuel generalizing q acc v4 v16 with
  | zero =>
    have hq : ¬ q + 1 ≤ src + n - 4 := by omega
    wasm_eval 13 [block_simp, cWrap, cOuter, cLoop, cLoopBody, cLocals, c_after3, igtU_ofNat, hq]
    · simp [TraceOK, AccessOK]
    · apply Until.done
      right
      refine ⟨rfl, ?_⟩
      simpa only [BContext.fill, cLocals] using
        c_err F st inst src dst n cap o' off (vI q) (q + 1) acc v16 (by omega) (by omega)
  | succ fuel ih =>
    by_cases hq : q + 1 ≤ src + n - 4
    · have hb : (mem.byte q).toNat ≤ 255 := by have := (mem.byte q).toNat_lt; omega
      have hsum : acc + (mem.byte q).toNat < 2 ^ 31 := by omega
      have hacc' : acc + (mem.byte q).toNat + 255 * fuel ≤ 255 * n := by omega
      by_cases h255 : (mem.byte q).toNat = 255
      · wasm_eval 24 [block_simp, cWrap, cOuter, cLoop, cLoopBody, cLocals, hm, hmem,
          igtU_ofNat, iltS_zero, h255]
        · simp [TraceOK, AccessOK, Span]
          intro x hx0 hx1
          left
          constructor <;> omega
        · have hi := ih (q + 1) (acc + 255) (vI (q + 1))
            (vI 255) (by omega) (by omega) (by omega) (by omega)
          apply hi.mono (fun _ hx => hx)
          intro c hc
          have hsum255 : acc + 255 < 2 ^ 31 := by omega
          have he : extM mem (src + n - 4) (fuel + 1) q acc =
              extM mem (src + n - 4) fuel (q + 1) (acc + 255) := by
            simp only [extM, hq, h255, hsum255, ite_true]
          simpa only [cResult, he] using hc
      · wasm_eval 24 [block_simp, cWrap, cOuter, cLoop, cLoopBody, cLocals, hm, hmem,
          igtU_ofNat, iltS_zero, h255]
        · simp [TraceOK, AccessOK, Span]
          intro x hx0 hx1
          left
          constructor <;> omega
        · apply (c_finish H F st inst ma src dst n cap o' off
            (acc + (mem.byte q).toNat) (q + 1) (vI (q + 1)) (vI (mem.byte q).toNat)
            hn (by omega) ho).mono (fun _ hx => hx)
          intro c hc
          left
          refine ⟨acc + (mem.byte q).toNat, q + 1, ?_, hc⟩
          simp only [extM, hq, hsum, h255, ite_true, ite_false]
    · wasm_eval 13 [block_simp, cWrap, cOuter, cLoop, cLoopBody, cLocals, c_after3, igtU_ofNat, hq]
      · simp [TraceOK, AccessOK]
      · apply Until.done
        right
        refine ⟨by simp only [extM, hq, ite_false], ?_⟩
        simpa only [BContext.fill, cLocals] using
          c_err F st inst src dst n cap o' off (vI q) (q + 1) acc v16 (by omega) (by omega)

theorem segC : SegC := by
  intro H F st inst ls ma mem src dst n cap o' off ml0 j hcl h4 h15 h17 h18 h2 hm hmem
    hsrc hdst hs hd hsize hj0 hjn hml ho
  obtain ⟨v3, v16, rfl⟩ := c_decompose hcl h4 h15 h17 h18 h2
  have hn : n ≤ 2097152 := by omega
  rw [c_code]
  change Until H _ _ ((ctx1 F).fill
    ⟨st, ⟨cLocals src dst n cap o' off v3 (vI j) ml0 v16, inst⟩, cOuter (cSegment.map .plain)⟩)
  by_cases hsmall : ml0 < 15
  · wasm_eval 4 [block_simp, cOuter, cSegment, cLocals, hsmall]
    · simp [TraceOK, AccessOK]
    · apply Until.done
      left
      refine ⟨hsmall, ?_⟩
      simpa only [BContext.fill, ctx5, ctx4, ctx2, Context.fill, cLocals] using
        c_atX4 F st inst src dst n cap o' off v3 j ml0 v16
  · have h15 : ml0 = 15 := by omega
    subst ml0
    by_cases hj : j + 1 ≤ src + n - 4
    · wasm_eval 12 [block_simp, cOuter, cSegment, cGuard, cLocals, hj]
      · simp [TraceOK, AccessOK]
      · have hn0 : 0 < n := by omega
        have hb : (mem.byte j).toNat ≤ 255 := by have := (mem.byte j).toNat_lt; omega
        by_cases h255 : (mem.byte j).toNat = 255
        · wasm_eval 10 [block_simp, cOuter, cExt, cFirst, cLocals, hm, hmem, h255]
          · simp [TraceOK, AccessOK, Span]
            intro x hx0 hx1
            left
            constructor <;> omega
          · have hext : extM mem (src + n - 4) n j 0 =
                extM mem (src + n - 4) (n - 1) (j + 1) 255 := by
              cases n with
              | zero => omega
              | succ n =>
                simp only [extM, hj, h255, Nat.zero_add, Nat.reducePow, Nat.reduceLT,
                  ite_true, Nat.add_sub_cancel]
            apply (c_loop H F st inst ma mem src dst n cap o' off (n - 1) (j + 1) 255
              (vI j) v16 hm hmem hs hsize ho (by omega) (by omega) (by omega) (by omega)).mono
              (fun _ hx => hx)
            intro c hc
            rcases hc with ⟨a, q, he, hx⟩ | ⟨he, hx⟩
            · right; left
              exact ⟨rfl, a, q, hext.trans he, hx⟩
            · right; right
              exact ⟨rfl, hext.trans he, hx⟩
        · wasm_eval 11 [block_simp, cOuter, cExt, cFirst, cLocals, hm, hmem, h255]
          · simp [TraceOK, AccessOK, Span]
            intro x hx0 hx1
            left
            constructor <;> omega
          · apply (c_footer H F st inst ma src dst n cap o' off (mem.byte j).toNat (j + 1)
              (vI (j + 1)) v16 hn (by omega) ho).mono (fun _ hx => hx)
            intro c hc
            right; left
            refine ⟨rfl, (mem.byte j).toNat, j + 1, ?_, hc⟩
            have hsum : (mem.byte j).toNat < 2 ^ 31 := by omega
            cases n with
            | zero => omega
            | succ n => simp only [extM, hj, Nat.zero_add, hsum, h255, ite_true, ite_false]
    · wasm_eval 14 [block_simp, cOuter, cSegment, cGuard, cLocals, hj]
      · simp [TraceOK, AccessOK]
      · apply Until.done
        right; right
        refine ⟨rfl, ?_, ?_⟩
        · cases n <;> simp only [extM, hj, ite_false]
        · simpa only [BContext.fill, cLocals] using
            c_err F st inst src dst n cap o' off (vI (j + 1)) (j + 1) 15 v16 (by omega) (by omega)

#print axioms segC

end Subjects.Lz4C.Eval
