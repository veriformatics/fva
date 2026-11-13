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
        obtain ⟨addr', fi, ha', hfi, hdt⟩ := hf.funcs hx
        have haddr := Option.some.inj (ha'.symm.trans ha)
        subst addr' hdt
        exact .single (.refFuncAddr hfi)

theorem ASeqT.refNull {s : Store} {C : Context} {ht : HeapType} {a b : List OpType}
    (h : ASeqT s C [.plain (.refNull ht)] ⟨a, b⟩) : ASeqT s C [.refNullAddr] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi =>
      cases hi with | refNull => exact .single .refNullAddr

theorem ASeqT.localGet {s : Store} {f : Frame} {C : Context} {x : Nat} {v : Val}
    {a b : List OpType} (hf : FrameCtx s f C)
    (h : ASeqT s C [.plain (.localGet x)] ⟨a, b⟩) (hv : f.locals[x]? = some (some v)) :
    ASeqT s C [v.instr] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi =>
      cases hi with | localGet hx hr =>
        obtain ⟨v', hv', ht⟩ := hf.locals hx hr
        have heq := Option.some.inj (Option.some.inj (hv'.symm.trans hv))
        subst v'
        exact (AInstrT.value ht)

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
            (Matches.refl _) (by rw [ASeqT.after_pure _ (ASeqT.vals_sets' _) (ASeqT.vals_dead' _)]
                                 exact .plain (.localSet hx))

theorem ASeqT.localSet {s : Store} {f : Frame} {C : Context} {x : Nat} {v : Val}
    {a b : List OpType} (hf : FrameCtx s f C)
    (h : ASeqT s C [v.instr, .plain (.localSet x)] ⟨a, b⟩) :
    ∃ C', FrameCtx s { f with locals := f.locals.set x v } C' ∧ (C.addSets [x]).Entails C' ∧
      ASeqT s C [] ⟨a, b⟩ := by
  obtain ⟨p, ts, out, hp, hout, hi, hvs⟩ := h.fixed_arity_inv (vs := [v]) (by
    intro x y hi
    cases hi with | plain hi => cases hi; rfl)
  cases hi with | plain hi =>
    cases hi with | localSet hx =>
      cases hvs with | cons hv hs =>
        obtain ⟨C', hf', he⟩ := hf.setLocal hx hv
        exact ⟨C', hf', he, ASeqT.nil_iff.mpr (hp.trans (by simpa using hout))⟩

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
        exact (AInstrT.value ((hok.globals g (List.mem_of_getElem? hg)).2.globalSub ht))

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
        have hval : g.type.val = _ := ht.2
        exact ⟨ht.1, by simpa only [hval, HasOpType] using hv, hp.trans (by simpa using hout)⟩

theorem ASeqT.refAsNonNull {s : Store} {C : Context} {r : Ref} {a b : List OpType}
    (hr : r ≠ .null) (h : ASeqT s C [(Val.ref r).instr, .plain .refAsNonNull] ⟨a, b⟩) :
    ASeqT s C [(Val.ref r).instr] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [.ref r])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi hvs
    cases hi with | plain hi =>
      cases hi with | @refAsNonNull _ hh =>
        cases hvs with | cons hv _ =>
          cases hh with
          | none => exact hv.elim
          | some hh => exact AInstrT.value (hv.nonNull hr)

end FVA.Wasm.Valid
