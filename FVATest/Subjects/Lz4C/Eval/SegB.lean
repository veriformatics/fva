import FVATest.Subjects.Lz4C.Eval.SegCommon
import FVATest.Subjects.Lz4C.Eval.ShortFacts
import FVATest.Subjects.Lz4C.Loop

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false

def bTest : List Instr :=
  [.localGet 3, .localGet 2, .ibinop .w32 .add, .localTee 17, .localGet 13,
    .irelop .w32 (.gt .u), .brIf 0, .localGet 4, .localGet 2, .ibinop .w32 .add,
    .localTee 18, .localGet 12, .irelop .w32 (.le .u), .brIf 1]

def bRet : List Instr := [.drop, .localGet 17, .localGet 1, .ibinop .w32 .sub, .return_]

def bNear : List Instr :=
  [.localGet 4, .localGet 2, .ibinop .w32 .add, .localGet 7, .irelop .w32 .ne,
    .brIf 6, .localGet 17, .localGet 5, .irelop .w32 (.gt .u), .brIf 6,
    .localGet 3, .localGet 4, .localGet 2, .call 4] ++ bRet

def bRoom : Instr := .block .empty (.block .empty bTest :: bNear)

def bOffset : List Instr :=
  [.localGet 16, .iconst .w32 15, .ibinop .w32 .and, .localSet 15, .localGet 18,
    .iconst .w32 2, .ibinop .w32 .add, .localSet 4, .localGet 17, .localGet 18,
    .loadPacked .w32 .p16 .u ⟨0, 0⟩, .localTee 18, .ibinop .w32 .sub, .localSet 2]

noncomputable def bAfterRoom : List Instr := body7.drop 2

theorem b_code : body7.drop 1 = bRoom :: bAfterRoom := by kernel_rfl

theorem b_offset_code : body7.drop 3 = bOffset := by kernel_rfl

noncomputable def bOuter (es : List AInstr) : List AInstr :=
  cOuter (.label 0 [] es :: (body6.drop 1).map .plain)

noncomputable def bCtx (caller : Frame) (rest : List AInstr) (outer : Context) : Context :=
  .label 0 [] (bAfterRoom.map .plain) (ctx7 (ctx2 (fnCtx caller rest outer)))

def bLs (src dst n cap op q len t : Nat) (v15 v17 v18 : Val) : List Val :=
  [vI src, vI dst, vI len, vI op, vI q, vI (dst + cap), vI (dst + cap - 32),
    vI (src + n), vI (src + n - 16), vI (dst + cap - 5), vI (dst + cap - 7),
    vI (src + n - 4), vI (src + n - 8), vI (dst + cap - 12), vI (src + n - 15),
    v15, vI t, v17, v18]

theorem b_const (src dst n cap op q len t : Nat) (v15 v17 v18 : Val) :
    ConstLocals (bLs src dst n cap op q len t v15 v17 v18) src dst n cap := by
  simp [ConstLocals, bLs]

theorem b_err (F : Context) (st : Store) (inst : ModuleInst) (src dst n cap op q len t : Nat)
    (v15 v17 v18 : Val) :
    ErrExit F st inst src dst n cap q
      ((ctx1 F).fill ⟨st, ⟨bLs src dst n cap op q len t v15 v17 v18, inst⟩,
        (body1.drop 54).map .plain⟩) :=
  ⟨_, b_const _ _ _ _ _ _ _ _ _ _ _, rfl, rfl⟩

/-- A return crosses the function's own labels and restores its caller frame. -/
theorem b_return {R W : Nat → Nat → Prop} (H : HostSem) (caller : Frame) (rest : List AInstr)
    (outer : Context) (st : Store) (inst : ModuleInst) (ls : List Val) (rv cpy dst : Nat)
    (h17 : ls[17]? = some (vI cpy)) (h1 : ls[1]? = some (vI dst))
    (hdst : dst < 2 ^ 32) (hle : dst ≤ cpy) :
    Until H (Within R W) (Returned caller rest outer st (cpy - dst))
      ((bCtx caller rest outer).fill ⟨st, ⟨ls, inst⟩, vals [vI rv] ++ bRet.map .plain⟩) := by
  change Until H _ _ (outer.fill ⟨st, caller,
    .frame 1 ⟨ls, inst⟩ [.label 1 [] (.label 0 []
      (bOuter (.label 0 [] (vals [vI rv] ++ bRet.map .plain) :: bAfterRoom.map .plain)) ::
        (Lifted.func2.body.drop 3).map .plain)] :: rest⟩)
  wasm_eval 5 [block_simp, bOuter, cOuter, bRet, h17, h1]
  · simp [TraceOK, AccessOK]
  · apply Until.done
    simp only [Returned, BContext.fill, vals, List.map_cons, List.map_nil, List.singleton_append]

noncomputable def bNearResult (caller : Frame) (rest : List AInstr) (outer : Context) (st : Store)
    (inst : ModuleInst) (mem : MemInst) (ma src dst n cap op q len : Nat) (c : Config) : Prop :=
  (q + len = src + n ∧ op + len ≤ dst + cap ∧
    Returned caller rest outer (st.setMem ma (move mem op q len)) (op + len - dst) c) ∨
  (¬ (q + len = src + n ∧ op + len ≤ dst + cap) ∧
    ErrExit (fnCtx caller rest outer) st inst src dst n cap q c)

/-- The near-end branch has no scratch writes before its memmove call. -/
theorem b_near (H : HostSem) (caller : Frame) (rest : List AInstr) (outer : Context)
    (st : Store) (inst : ModuleInst) (mem : MemInst) (a4 ma src dst n cap op q len t : Nat)
    (v15 v18 : Val)
    (hcall4 : inst.funcs[4]? = some a4)
    (hfun4 : st.funcs[a4]? = some (.wasm copyType inst Lifted.func4))
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hs : src + n ≤ mem.size) (hd : dst + cap ≤ mem.size) (hsize : mem.size ≤ 2097152)
    (hq0 : src ≤ q) (hqn : q ≤ src + n) (hop0 : dst ≤ op) (hopn : op ≤ dst + cap)
    (hlen : len < 2 ^ 31) :
    Until H
      (Within (fun m x => m = ma ∧ (Span ma src n m x ∨ Span ma dst cap m x)) (Span ma dst cap))
      (bNearResult caller rest outer st inst mem ma src dst n cap op q len)
      ((ctx1 (fnCtx caller rest outer)).fill
        ⟨st, ⟨bLs src dst n cap op q len t v15 (vI (op + len)) v18, inst⟩,
          bOuter (.label 0 [] (bNear.map .plain) :: bAfterRoom.map .plain)⟩) := by
  by_cases he : q + len = src + n
  · wasm_eval 6 [block_simp, bOuter, cOuter, bNear, bLs, he]
    · simp [TraceOK, AccessOK]
    · by_cases hc : op + len ≤ dst + cap
      · wasm_eval 4 [block_simp, bOuter, cOuter, bNear, bLs, igtU_ofNat, hc]
        · simp [TraceOK, AccessOK]
        · wasm_eval 3 [block_simp, bLs]
          · simp [TraceOK, AccessOK]
          · change Until H _ _ ((bCtx caller rest outer).fill
              ⟨st, ⟨bLs src dst n cap op q len t v15 (vI (op + len)) v18, inst⟩,
                vals [vI op, vI q, vI len] ++ [.plain (.call 4)] ++ bRet.map .plain⟩)
            have hmove := s2 H (bCtx caller rest outer) st
              ⟨bLs src dst n cap op q len t v15 (vI (op + len)) v18, inst⟩ []
              (bRet.map .plain) a4 ma inst mem op q len hcall4 hfun4 hm hmem (by omega)
              (by omega) (by omega)
            refine Until.trans (hmove.mono (fun c hw => ?_) (fun _ hx => hx)) ?_
            · refine ⟨fun m x hx => ?_, fun m x hx => ?_⟩
              · obtain ⟨rfl, hlo, hhi⟩ := hw.1 m x hx
                exact ⟨rfl, .inl ⟨rfl, by omega, by omega⟩⟩
              · obtain ⟨rfl, hlo, hhi⟩ := hw.2 m x hx
                exact ⟨rfl, by omega, by omega⟩
            · intro c hc'
              subst c
              apply (b_return H caller rest outer (st.setMem ma (move mem op q len)) inst
                (bLs src dst n cap op q len t v15 (vI (op + len)) v18) op (op + len) dst
                (by rfl) (by rfl) (by omega) (by omega)).mono (fun _ hx => hx)
              intro c hr
              exact .inl ⟨he, hc, hr⟩
      · wasm_eval 5 [block_simp, bOuter, cOuter, bNear, bLs, igtU_ofNat, hc]
        · simp [TraceOK, AccessOK]
        · apply Until.done
          right
          refine ⟨fun h => hc h.2, ?_⟩
          simpa only [BContext.fill, bLs] using
            b_err (fnCtx caller rest outer) st inst src dst n cap op q len t v15 (vI (op + len)) v18
  · wasm_eval 7 [block_simp, bOuter, cOuter, bNear, bLs, he]
    · simp [TraceOK, AccessOK]
    · apply Until.done
      right
      refine ⟨fun h => he h.1, ?_⟩
      simpa only [BContext.fill, bLs] using
        b_err (fnCtx caller rest outer) st inst src dst n cap op q len t v15 (vI (op + len)) v18

theorem segB : SegB := by
  intro H caller rest outer st inst ls a a4 ma mem src dst n cap op q len t hcl h3 h4 h2 h16
    hcall hfun hcall4 hfun4 hm hmem hsrc hdst hs hd hsize hsep hq0 hqn hop0 hopn hlen
  obtain ⟨u2, u15, u16, u17, u18, rfl⟩ := head_decompose (HeadLocals.of_const hcl h3 h4)
  simp only [wasm_step] at h2 h16
  subst u2
  subst u16
  let F := fnCtx caller rest outer
  let ls0 := bLs src dst n cap op q len t u15 u17 u18
  have near_case (v18 : Val) (hn : dst + cap < op + len + 12 ∨ src + n < q + len + 8) :
      Until H
        (Within (fun m x => m = ma ∧ (Span ma src n m x ∨ Span ma dst cap m x)) (Span ma dst cap))
        (SegBExit caller rest outer st inst ls0 ma mem src dst n cap op q len t)
        ((ctx1 F).fill
          ⟨st, ⟨bLs src dst n cap op q len t u15 (vI (op + len)) v18, inst⟩,
            bOuter (.label 0 [] (bNear.map .plain) :: bAfterRoom.map .plain)⟩) := by
    apply (b_near H caller rest outer st inst mem a4 ma src dst n cap op q len t u15 v18
      hcall4 hfun4 hm hmem hs hd hsize hq0 hqn hop0 hopn hlen).mono (fun _ hx => hx)
    intro c hc
    rcases hc with ⟨he, hc, hr⟩ | ⟨he, herr⟩
    · exact .inl ⟨hn, he, hc, hr⟩
    · exact .inr (.inl ⟨hn, he, herr⟩)
  rw [b_code]
  change Until H _ (SegBExit caller rest outer st inst ls0 ma mem src dst n cap op q len t)
    ((ctx1 F).fill ⟨st, ⟨ls0, inst⟩, bOuter (.plain bRoom :: bAfterRoom.map .plain)⟩)
  by_cases hO : dst + cap < op + len + 12
  · wasm_eval 11 [block_simp, bOuter, cOuter, bRoom, bTest, bLs, ls0, igtU_ofNat, hO]
    · simp [TraceOK, AccessOK]
    · simpa only [BContext.fill, bOuter, cOuter, bLs, List.singleton_append] using
        near_case u18 (.inl hO)
  · by_cases hI : src + n < q + len + 8
    · wasm_eval 19 [block_simp, bOuter, cOuter, bRoom, bTest, bLs, ls0, igtU_ofNat, hO, hI]
      · simp [TraceOK, AccessOK]
      · simpa only [BContext.fill, bOuter, cOuter, bLs, List.singleton_append] using
          near_case (vI (q + len)) (.inr hI)
    · wasm_eval 19 [block_simp, bOuter, cOuter, bRoom, bTest, bLs, ls0, igtU_ofNat, hO, hI]
      · simp [TraceOK, AccessOK]
      · have hk := chunks_spec (q := op) (e := op + len) (by omega)
        have hcopy : 8 * chunks op (op + len) ≤ len + 8 := by
          rcases hk.2.2 with h1 | hp
          · rw [h1]; omega
          · omega
        have hreadEnd : q + 8 * chunks op (op + len) ≤ src + n := by omega
        have hwriteEnd : op + 8 * chunks op (op + len) ≤ dst + cap := by omega
        change Until H _ _ ((ctx7 (ctx2 F)).fill
          ⟨st, ⟨bLs src dst n cap op q len t u15 (vI (op + len)) (vI (q + len)), inst⟩,
            (body7.drop 2).map .plain⟩)
        have hw := s3 (ctx2 F) H st inst
          (bLs src dst n cap op q len t u15 (vI (op + len)) (vI (q + len))) a ma mem
          op q (op + len) (by rfl) (by rfl) (by rfl) hcall hfun hm hmem (by omega)
          (by omega) (by omega) (by omega)
        refine Until.trans (hw.mono (fun c hw' => ?_) (fun _ hx => hx)) ?_
        · refine ⟨fun m x hx => ?_, fun m x hx => ?_⟩
          · obtain ⟨rfl, hlo, hhi⟩ := hw'.1 m x hx
            exact ⟨rfl, .inl ⟨rfl, by omega, by omega⟩⟩
          · obtain ⟨rfl, hlo, hhi⟩ := hw'.2 m x hx
            exact ⟨rfl, by omega, by omega⟩
        · intro c hc
          subst c
          let off := (mem.byte (q + len)).toNat + 256 * (mem.byte (q + len + 1)).toNat
          have hoff : off < 65536 := off_lt mem (q + len)
          have hread : (fwdCopy mem op q (8 * chunks op (op + len))).read (q + len) 2 = off := by
            rw [read_two,
              copy_source_byte mem src dst n cap op q (8 * chunks op (op + len)) (q + len)
                hsep hop0 hwriteEnd (by omega) (by omega),
              copy_source_byte mem src dst n cap op q (8 * chunks op (op + len)) (q + len + 1)
                hsep hop0 hwriteEnd (by omega) (by omega)]
          have hM := ofNat32_sub (a := op + len) (b := off) (by omega) (by omega)
          dsimp only [off] at hM
          change Until H _ _ ((ctx6 (ctx2 F)).fill ⟨_, _,
            .label 0 [] ((body7.drop 3).map .plain) :: (body6.drop 1).map .plain⟩)
          wasm_eval 14 [block_simp, b_offset_code, bOffset, bLs, hm, hmem, hread]
          · simp [TraceOK, AccessOK, Span]
            intro x hx0 hx1
            left
            constructor <;> omega
          · apply Until.done
            right; right
            refine ⟨fun h => h.elim hO hI, ?_⟩
            simp only [wasm_step, hM, BContext.fill, ls0, bLs]
            rfl

#print axioms segB

end Subjects.Lz4C.Eval
