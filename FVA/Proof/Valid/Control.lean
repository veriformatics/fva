import FVA.Proof.Valid.Table

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

theorem Matches.ops_eq {ts us : List ValType} (h : Matches (ops ts) (ops us)) : ts = us := by
  induction ts generalizing us with
  | nil => cases us with
    | nil => rfl
    | cons u us => cases h
  | cons t ts ih =>
    cases us with
    | nil => cases h
    | cons u us =>
      cases h with | cons ht hs =>
        exact congrArg₂ List.cons ht (ih hs)

theorem hasOp_ops_iff {s : Store} {vs : List Val} {ts : List ValType} :
    List.Forall₂ (HasOpType s) vs (ops ts) ↔ List.Forall₂ (Val.HasType s) vs ts :=
  List.forall₂_map_right_iff

theorem i32_type {s : Store} {v : BitVec 32} {t : ValType}
    (h : (Val.i32 v).HasType s t) : t = .num .i32 := by
  cases t with
  | num n => cases n <;> simp_all [Val.HasType]
  | ref r => cases h

theorem ASeqT.i32_prefix {s : Store} {C : Context} {v : BitVec 32} {es : List AInstr}
    {a b : List OpType} (h : ASeqT s C ((Val.i32 v).instr :: es) ⟨a, b⟩) :
    ASeqT s C es ⟨a ++ [i32], b⟩ := by
  obtain ⟨ts, hvs, he⟩ := h.value_prefix_inv (vs := [.i32 v])
  cases hvs with | cons hv hs =>
    cases hs
    have ht := i32_type hv
    subst ht
    exact he

theorem ASeqT.drop_selector {s : Store} {C : Context} {v : BitVec 32} {e : AInstr}
    {out : List AInstr} {a b : List OpType}
    (h : ASeqT s C [(Val.i32 v).instr, e] ⟨a, b⟩)
    (replacement : ∀ {x y}, AInstrT s C e ⟨x, y⟩ →
      ∃ params, x = params ++ [i32] ∧ ASeqT s C out ⟨params, y⟩) :
    ASeqT s C out ⟨a, b⟩ := by
  obtain ⟨p, x, y, z, hin, hout, hm, hi⟩ := ASeqT.single_iff.mp h.i32_prefix
  obtain ⟨params, rfl, hnew⟩ := replacement hi
  have harg := hin.trans ((Matches.refl p).append hm)
  have hp : Matches a (p ++ params) :=
    (Matches.append_inv (by simpa only [List.append_assoc] using harg) rfl).1
  have hn := hnew.frame p
  exact .sub (hn.input hp) hout

theorem ASeqT.nop {s : Store} {C : Context} {a b : List OpType}
    (h : ASeqT s C [.plain .nop] ⟨a, b⟩) : ASeqT s C [] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi => cases hi; exact .nil

theorem ASeqT.block {s : Store} {f : Frame} {C : Context} {bt : BlockType}
    {body : List Instr} {ft : FuncType} {vs : List Val} {a b : List OpType}
    (hf : FrameCtx s f C) (h : ASeqT s C (vals vs ++ [.plain (.block bt body)]) ⟨a, b⟩)
    (hbt : bt.expand f = some ft) (hlen : vs.length = ft.params.length) :
    ASeqT s C [.label ft.results.length [] (vals vs ++ body.map .plain)] ⟨a, b⟩ := by
  apply h.replace_fixed
  · intro x y hi
    cases hi with | plain hi =>
      cases hi with | block hb hs =>
        have heq := Option.some.inj (hb.symm.trans ((hf.blockType bt).trans hbt))
        subst heq
        simpa only [ops, List.length_map] using hlen
  · intro x y hi hvs
    cases hi with | plain hi =>
      cases hi with | block hb hs =>
        have heq := Option.some.inj (hb.symm.trans ((hf.blockType bt).trans hbt))
        subst heq
        exact .single (.label rfl .nil
          ((ASeqT.values (hasOp_ops_iff.mp hvs)).append (ASeqT.plain hs)))

theorem ASeqT.loop {s : Store} {f : Frame} {C : Context} {bt : BlockType}
    {body : List Instr} {ft : FuncType} {vs : List Val} {a b : List OpType}
    (hf : FrameCtx s f C) (h : ASeqT s C (vals vs ++ [.plain (.loop bt body)]) ⟨a, b⟩)
    (hbt : bt.expand f = some ft) (hlen : vs.length = ft.params.length) :
    ASeqT s C [.label ft.params.length [.loop bt body] (vals vs ++ body.map .plain)]
      ⟨a, b⟩ := by
  apply h.replace_fixed
  · intro x y hi
    cases hi with | plain hi =>
      cases hi with | loop hb hs =>
        have heq := Option.some.inj (hb.symm.trans ((hf.blockType bt).trans hbt))
        subst heq
        simpa only [ops, List.length_map] using hlen
  · intro x y hi hvs
    cases hi with | plain hi =>
      cases hi with | loop hb hs =>
        have heq := Option.some.inj (hb.symm.trans ((hf.blockType bt).trans hbt))
        subst heq
        exact .single (.label rfl (SeqT.single (.loop hb hs))
          ((ASeqT.values (hasOp_ops_iff.mp hvs)).append (ASeqT.plain hs)))

theorem ASeqT.ifTrue {s : Store} {C : Context} {bt : BlockType} {thn els : List Instr}
    {v : BitVec 32} {a b : List OpType}
    (h : ASeqT s C [(Val.i32 v).instr, .plain (.if_ bt thn els)] ⟨a, b⟩) :
    ASeqT s C [.plain (.block bt thn)] ⟨a, b⟩ := by
  apply h.drop_selector
  intro x y hi
  cases hi with | plain hi =>
    cases hi with | if_ hb h₁ _ => exact ⟨_, rfl, .single (.plain (.block hb h₁))⟩

theorem ASeqT.ifFalse {s : Store} {C : Context} {bt : BlockType} {thn els : List Instr}
    {v : BitVec 32} {a b : List OpType}
    (h : ASeqT s C [(Val.i32 v).instr, .plain (.if_ bt thn els)] ⟨a, b⟩) :
    ASeqT s C [.plain (.block bt els)] ⟨a, b⟩ := by
  apply h.drop_selector
  intro x y hi
  cases hi with | plain hi =>
    cases hi with | if_ hb _ h₂ => exact ⟨_, rfl, .single (.plain (.block hb h₂))⟩

theorem ASeqT.brIfTrue {s : Store} {C : Context} {l : Nat} {v : BitVec 32}
    {a b : List OpType} (h : ASeqT s C [(Val.i32 v).instr, .plain (.brIf l)] ⟨a, b⟩) :
    ASeqT s C [.plain (.br l)] ⟨a, b⟩ := by
  apply h.drop_selector
  intro x y hi
  cases hi with | plain hi =>
    cases hi with | brIf hb => exact ⟨_, rfl, .single (.plain (.br (t₁ := []) hb))⟩

theorem ASeqT.brIfFalse {s : Store} {C : Context} {l : Nat} {v : BitVec 32}
    {a b : List OpType} (h : ASeqT s C [(Val.i32 v).instr, .plain (.brIf l)] ⟨a, b⟩) :
    ASeqT s C [] ⟨a, b⟩ := by
  apply h.drop_selector
  intro x y hi
  cases hi with | plain hi =>
    cases hi with | brIf hb => exact ⟨_, rfl, .nil⟩

theorem ASeqT.brTable {s : Store} {C : Context} {ls : List Nat} {l : Nat} {v : BitVec 32}
    {a b : List OpType}
    (h : ASeqT s C [(Val.i32 v).instr, .plain (.brTable ls l)] ⟨a, b⟩) :
    ASeqT s C [.plain (.br (ls[v.toNat]?.getD l))] ⟨a, b⟩ := by
  apply h.drop_selector
  intro x y hi
  cases hi with | plain hi =>
    cases hi with | brTable hb =>
      have hmem : ls[v.toNat]?.getD l ∈ l :: ls := by
        cases hv : ls[v.toNat]? with
        | none => exact List.mem_cons_self
        | some k => exact List.mem_cons_of_mem l (List.mem_of_getElem? hv)
      obtain ⟨ts, ht, hm⟩ := hb _ hmem
      exact ⟨_, rfl, (ASeqT.single (.plain (.br ht))).input ((Matches.refl _).append hm)⟩

theorem ASeqT.call {s : Store} {f : Frame} {C : Context} {x addr : Nat}
    {a b : List OpType} (hf : FrameCtx s f C)
    (h : ASeqT s C [.plain (.call x)] ⟨a, b⟩) (ha : f.inst.funcs[x]? = some addr) :
    ASeqT s C [.invoke addr] ⟨a, b⟩ := by
  obtain ⟨p, x, y, z, hin, hout, hm, hi⟩ := ASeqT.single_iff.mp h
  cases hi with | plain hi =>
    cases hi with | call hx =>
      obtain ⟨addr', fi, ha', hfi, ht⟩ := hf.funcs hx
      have heq := Option.some.inj (ha'.symm.trans ha)
      subst addr'
      apply ASeqT.single_iff.mpr
      refine ⟨p, x, _, _, hin, hout, hm, ?_⟩
      simpa only [ht] using AInstrT.invoke (C := C) hfi

theorem ASeqT.callIndirect {s : Store} {f : Frame} {C : Context} {x y addr : Nat}
    {v : BitVec 32} {a b : List OpType} (hf : FrameCtx s f C)
    (h : ASeqT s C [(Val.i32 v).instr, .plain (.callIndirect x y)] ⟨a, b⟩)
    (htarget : CallTarget s f x y v addr) : ASeqT s C [.invoke addr] ⟨a, b⟩ := by
  apply h.drop_selector
  intro ins out hi
  cases hi with | plain hi =>
    cases hi with | callIndirect _ _ hy =>
      obtain ⟨ta, ti, fi, ft, _, _, _, hfi, hft, he⟩ := htarget
      have hct : C.types[y]? = some ft := (hf.blockType (.idx y)).trans hft
      have heq := Option.some.inj (hy.symm.trans hct)
      have hfiType := he.trans heq.symm
      refine ⟨_, rfl, .single ?_⟩
      simpa only [hfiType] using AInstrT.invoke (C := C) hfi

end FVA.Wasm.Valid
