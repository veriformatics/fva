import FVA.Proof.Valid.Redex

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

theorem ASeqT.refFunc {s : Store} {f : Frame} {C : Context} {x addr : Nat}
    {a b : List OpType} (hf : FrameCtx s f C)
    (h : ASeqT s C [.plain (.refFunc x)] ⟨a, b⟩) (ha : f.inst.funcs[x]? = some addr) :
    ASeqT s C [.refFuncAddr addr] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi =>
      cases hi with | refFunc hx _ =>
        obtain ⟨addr', fi, ha', hfi, _⟩ := hf.funcs hx
        have haddr := Option.some.inj (ha'.symm.trans ha)
        subst addr'
        exact .single (.refFuncAddr (List.getElem?_eq_some_iff.mp hfi).1)

theorem ASeqT.localGet {s : Store} {f : Frame} {C : Context} {x : Nat} {v : Val}
    {a b : List OpType} (hf : FrameCtx s f C)
    (h : ASeqT s C [.plain (.localGet x)] ⟨a, b⟩) (hv : f.locals[x]? = some v) :
    ASeqT s C [v.instr] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi =>
      cases hi with | localGet hx =>
        obtain ⟨v', hv', ht⟩ := hf.locals hx
        have heq := Option.some.inj (hv'.symm.trans hv)
        subst v'
        exact .single (.value ht)

theorem ASeqT.localTee {s : Store} {C : Context} {x : Nat} {v : Val}
    {a b : List OpType} (h : ASeqT s C [v.instr, .plain (.localTee x)] ⟨a, b⟩) :
    ASeqT s C [v.instr, v.instr, .plain (.localSet x)] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [v])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi hvs
    cases hi with | plain hi =>
      cases hi with | localTee hx =>
        cases hvs with | cons hv hs =>
          exact .snoc (t₀ := [_]) (.values (.cons hv (.cons hv .nil)))
            (Matches.refl _) (.plain (.localSet hx))

theorem ASeqT.localSet {s : Store} {f : Frame} {C : Context} {x : Nat} {v : Val}
    {a b : List OpType} (hf : FrameCtx s f C)
    (h : ASeqT s C [v.instr, .plain (.localSet x)] ⟨a, b⟩) :
    FrameCtx s { f with locals := f.locals.set x v } C ∧ ASeqT s C [] ⟨a, b⟩ := by
  obtain ⟨p, ts, out, hp, hout, hi, hvs⟩ := h.fixed_arity_inv (vs := [v]) (by
    intro x y hi
    cases hi with | plain hi => cases hi; rfl)
  cases hi with | plain hi =>
    cases hi with | localSet hx =>
      cases hvs with | cons hv hs =>
        exact ⟨hf.setLocal hx hv, ASeqT.nil_iff.mpr (hp.trans (by simpa using hout))⟩

theorem ASeqT.globalGet {s : Store} {f : Frame} {C : Context} {x addr : Nat}
    {g : GlobalInst} {a b : List OpType} (hok : StoreOK s) (hf : FrameCtx s f C)
    (h : ASeqT s C [.plain (.globalGet x)] ⟨a, b⟩)
    (ha : f.inst.globals[x]? = some addr) (hg : s.globals[addr]? = some g) :
    ASeqT s C [g.value.instr] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi =>
      cases hi with | globalGet hx =>
        obtain ⟨addr', gi, ha', hgi, ht⟩ := hf.globals hx
        have heqa := Option.some.inj (ha'.symm.trans ha)
        subst addr'
        have heqg := Option.some.inj (hgi.symm.trans hg)
        subst gi
        exact .single (.value (ht ▸ hok.globals g (List.mem_of_getElem? hg)))

theorem ASeqT.globalSet {s : Store} {f : Frame} {C : Context} {x addr : Nat}
    {g : GlobalInst} {v : Val} {a b : List OpType} (hf : FrameCtx s f C)
    (h : ASeqT s C [v.instr, .plain (.globalSet x)] ⟨a, b⟩)
    (ha : f.inst.globals[x]? = some addr) (hg : s.globals[addr]? = some g) :
    g.type.mutability = .var ∧ v.HasType s g.type.val ∧ Matches a b := by
  obtain ⟨p, ts, out, hp, hout, hi, hvs⟩ := h.fixed_arity_inv (vs := [v]) (by
    intro x y hi
    cases hi with | plain hi => cases hi; rfl)
  cases hi with | plain hi =>
    cases hi with | globalSet hx =>
      cases hvs with | cons hv hs =>
        obtain ⟨addr', gi, ha', hgi, ht⟩ := hf.globals hx
        have heqa := Option.some.inj (ha'.symm.trans ha)
        subst addr'
        have heqg := Option.some.inj (hgi.symm.trans hg)
        subst gi
        exact ⟨congrArg GlobalType.mutability ht,
          by simpa only [ht, HasOpType] using hv, hp.trans (by simpa using hout)⟩

end FVA.Wasm.Valid
