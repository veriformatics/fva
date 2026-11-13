import FVA.Proof.Valid.Call

/-!
# Exception and tail-call redexes (contract U28c T3)

Typing facts behind preservation's `try_table`, `throw`, catch-clause and `return_invoke` cases:
a tag index the frame context types names a store tag of that type; an exception's fields are
typed by its tag's parameters (`StoreOK.exns`); a catch clause's branch receives them at its
label's types; a tail call's arguments sit at the callee's parameter types and its results
match the frame's return type, whatever labels and handlers lie between.
-/

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

theorem FrameCtx.tagType {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C)
    {x : Nat} {ft : FuncType} (hx : C.tagType x = some ft) :
    ∃ a ti, f.inst.tags[x]? = some a ∧ s.tags[a]? = some ti ∧ ti.type.expand = some ft := by
  simp only [Context.tagType, Option.bind_eq_some_iff] at hx
  obtain ⟨dt, hdt, he⟩ := hx
  obtain ⟨a, ti, ha, hti, rfl⟩ := h.tags hdt
  exact ⟨a, ti, ha, hti, he⟩

/-- The tag the frame resolves `x` to is the one the context types `x` by. -/
theorem FrameCtx.tag_eq {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C)
    {x ta : Nat} {ti : TagInst} {ft : FuncType} (hx : C.tagType x = some ft)
    (hta : f.inst.tags[x]? = some ta) (hti : s.tags[ta]? = some ti) :
    ti.type.expand = some ft := by
  obtain ⟨a, ti', ha, hti', he⟩ := h.tagType hx
  have hat : a = ta := Option.some.inj (ha.symm.trans hta)
  subst hat
  have htt : ti' = ti := Option.some.inj (hti'.symm.trans hti)
  subst htt
  exact he

/-- A caught exception's fields have the types of the parameters its clause's tag declares. -/
theorem StoreOK.fields {s : Store} {f : Frame} {C : Context} (hok : StoreOK s)
    (hf : FrameCtx s f C) {a x : Nat} {e : ExnInst} {ts : List ValType}
    (he : s.exns[a]? = some e) (hx : f.inst.tags[x]? = some e.tag)
    (ht : C.tagType x = some ⟨ts, []⟩) : List.Forall₂ (Val.HasType s) e.fields ts := by
  obtain ⟨ti, ts', hti, hts', hfs⟩ := hok.exns e (List.mem_of_getElem? he)
  have hts := hf.tag_eq ht hx hti
  rw [hts'] at hts
  cases hts
  exact hfs

namespace ASeqT

theorem tryTable {s : Store} {f : Frame} {C : Context} {bt : BlockType} {cs : List Catch}
    {body : List Instr} {ft : FuncType} {vs : List Val} {a b : List OpType}
    (hf : FrameCtx s f C) (h : ASeqT s C (vals vs ++ [.plain (.tryTable bt cs body)]) ⟨a, b⟩)
    (hbt : bt.expand f = some ft) (hlen : vs.length = ft.params.length) :
    ASeqT s C [.handler ft.results.length cs
      [.label ft.results.length [] (vals vs ++ body.map .plain)]] ⟨a, b⟩ := by
  apply h.replace_fixed
  · intro x y hi
    cases hi with | plain hi =>
      cases hi with | tryTable hb hs hc =>
        obtain ⟨ft', hft', hp, -⟩ := hf.blockType hb
        rw [hbt] at hft'
        cases hft'
        simpa only [ops, List.length_map, ← hp] using hlen
  · intro x y hi hvs
    cases hi with | plain hi =>
      cases hi with | tryTable hb hs hc =>
        obtain ⟨ft', hft', -, hr⟩ := hf.blockType hb
        rw [hbt] at hft'
        cases hft'
        exact .single (.handler hc (.single (.label hr.symm .nil
          ((ASeqT.values (hasOp_ops_iff.mp hvs)).append_pure (ASeqT.plain hs)))))

/-- `throw x`'s operands have the types of tag `x`'s parameters. -/
theorem throw_args {s : Store} {C : Context} {vs : List Val} {x : Nat}
    {a b : List OpType} {ts : List ValType}
    (h : ASeqT s C (vals vs ++ [.plain (.throw x)]) ⟨a, b⟩)
    (ht : C.tagType x = some ⟨ts, []⟩) (hlen : vs.length = ts.length) :
    List.Forall₂ (Val.HasType s) vs ts := by
  obtain ⟨p, x', y, z, hout, hs, hm, hi⟩ := ASeqT.snoc_iff.mp h
  cases hi with | plain hi =>
    cases hi with | @throw _ _ ts' t₁ t₂ hb =>
      have heq : ts' = ts := by
        have h' := Option.some.inj (hb.symm.trans ht)
        cases h'
        rfl
      subst ts'
      obtain ⟨vts, hv, hvs⟩ := hs.values_inv
      have hh : Matches (a ++ ops vts) ((p ++ t₁) ++ ops ts) := by
        simpa only [List.append_assoc] using hv.trans ((Matches.refl p).append hm)
      have hlen' : (ops vts).length = (ops ts).length := by
        simp only [ops, List.length_map]
        exact hvs.length_eq.symm.trans hlen
      exact values_sub hvs (hh.append_inv hlen').2.ops_sub

/-- Values of a label's types followed by a branch to it: typed at any stack type (the branch
never falls through). -/
theorem vals_br {s : Store} {C : Context} {vs : List Val} {l : Nat} {ts : List ValType}
    (hvs : List.Forall₂ (Val.HasType s) vs ts) (hl : C.labels[l]? = some ts) (a b : List OpType) :
    ASeqT s C (vals vs ++ [.plain (.br l)]) ⟨a, b⟩ :=
  (ASeqT.values hvs a).append_pure (.single (.plain (.br (t₁ := a) (t₂ := b) hl)))
    (ASeqT.vals_sets' vs) (ASeqT.vals_dead' vs)

theorem returnInvoke_args {s : Store} {C : Context} {vs : List Val} {a : Nat}
    {a₀ b : List OpType} {fn : FuncInst} {ft : FuncType} {ts : List ValType}
    (h : ASeqT s C (vals vs ++ [.returnInvoke a]) ⟨a₀, b⟩)
    (hr : C.return_ = some ts) (hfn : s.funcs[a]? = some fn) (hft : fn.type.expand = some ft)
    (hlen : vs.length = ft.params.length) :
    List.Forall₂ (Val.HasType s) vs ft.params ∧ ResultSub ft.results ts := by
  obtain ⟨p, x, y, z, hout, hs, hm, hi⟩ := ASeqT.snoc_iff.mp h
  cases hi with | @returnInvoke _ _ fi ft' rs t₃ t₄ hfi hft' hr' hsub =>
    have hfi' : fi = fn := Option.some.inj (hfi.symm.trans hfn)
    subst hfi'
    have hft'' : ft' = ft := Option.some.inj (hft'.symm.trans hft)
    subst hft''
    have hrs : rs = ts := Option.some.inj (hr'.symm.trans hr)
    subst hrs
    obtain ⟨vts, hv, hvs⟩ := hs.values_inv
    have hh : Matches (a₀ ++ ops vts) ((p ++ t₃) ++ ops ft'.params) := by
      simpa only [List.append_assoc] using hv.trans ((Matches.refl p).append hm)
    have hlen' : (ops vts).length = (ops ft'.params).length := by
      simp only [ops, List.length_map]
      exact hvs.length_eq.symm.trans hlen
    exact ⟨values_sub hvs (hh.append_inv hlen').2.ops_sub, hsub⟩

/-- A typed pending throw names an existing exception. -/
theorem throwing_addr {s : Store} {C : Context} {pre post : List AInstr} {a : Nat}
    {x y : List OpType} (h : ASeqT s C (pre ++ throwing a ++ post) ⟨x, y⟩) :
    a < s.exns.length := by
  obtain ⟨x', y', he⟩ := h.fragment
  obtain ⟨p, x'', y'', z, -, -, hi, -⟩ := ASeqT.cons_iff.mp he
  cases hi with | refExnAddr ha => exact ha

/-- `throw x` allocates its exception: the store grows and stays valid. -/
theorem throw_store {s : Store} {f : Frame} {C : Context} {x ta : Nat} {ti : TagInst}
    {ft : FuncType} {vs : List Val} {a b : List OpType} (hok : StoreOK s) (hf : FrameCtx s f C)
    (h : ASeqT s C (vals vs ++ [.plain (.throw x)]) ⟨a, b⟩)
    (hta : f.inst.tags[x]? = some ta) (hti : s.tags[ta]? = some ti)
    (hft : ti.type.expand = some ft) (hres : ft.results = [])
    (hlen : vs.length = ft.params.length) :
    s.Extends { s with exns := s.exns ++ [⟨ta, vs⟩] } ∧
      StoreOK { s with exns := s.exns ++ [⟨ta, vs⟩] } := by
  obtain ⟨ps, rs⟩ := ft
  subst hres
  obtain ⟨p, x', y, z, hout, hs, hm, hi⟩ := ASeqT.snoc_iff.mp h
  have htt : C.tagType x = some ⟨ps, []⟩ := by
    cases hi with | plain hi =>
      cases hi with | throw hb =>
        have h' := hf.tag_eq hb hta hti
        rw [hft] at h'
        cases h'
        exact hb
  exact hok.addExn hti hft (h.throw_args htt hlen)

/-- `catch x l` takes the exception: its fields, then a branch to `l`. -/
theorem catchTag {s : Store} {f : Frame} {C : Context} {n a x l : Nat} {cs : List Catch}
    {e : ExnInst} {a₀ b : List OpType} (hok : StoreOK s) (hf : FrameCtx s f C)
    (h : ASeqT s C [.handler n (.tag x l :: cs) (throwing a)] ⟨a₀, b⟩)
    (he : s.exns[a]? = some e) (hx : f.inst.tags[x]? = some e.tag) :
    ASeqT s C (vals e.fields ++ [.plain (.br l)]) ⟨a₀, b⟩ := by
  apply h.replace_fixed (vs := [])
  · intro x' y hi
    cases hi; rfl
  · intro x' y hi _
    cases hi with | handler hcs hb =>
      obtain ⟨ts, lts, htt, hl, hsub⟩ := hcs _ (List.mem_cons_self ..)
      exact vals_br (values_sub (hok.fields hf he hx htt) hsub) hl _ _

/-- `catch_ref x l`: the fields and the exception's reference, then a branch to `l`. -/
theorem catchTagRef {s : Store} {f : Frame} {C : Context} {n a x l : Nat} {cs : List Catch}
    {e : ExnInst} {a₀ b : List OpType} (hok : StoreOK s) (hf : FrameCtx s f C)
    (h : ASeqT s C [.handler n (.tagRef x l :: cs) (throwing a)] ⟨a₀, b⟩)
    (he : s.exns[a]? = some e) (hx : f.inst.tags[x]? = some e.tag) :
    ASeqT s C (vals e.fields ++ [.refExnAddr a, .plain (.br l)]) ⟨a₀, b⟩ := by
  have hrw : vals e.fields ++ [.refExnAddr a, .plain (.br l)] =
      vals (e.fields ++ [.ref (.exn a)]) ++ [.plain (.br l)] := by
    simp [vals, Val.instr]
  rw [hrw]
  apply h.replace_fixed (vs := [])
  · intro x' y hi
    cases hi; rfl
  · intro x' y hi _
    cases hi with | handler hcs hb =>
      obtain ⟨ts, lts, htt, hl, hsub⟩ := hcs _ (List.mem_cons_self ..)
      have hvs : List.Forall₂ (Val.HasType s) (e.fields ++ [.ref (.exn a)])
          (ts ++ [exnNonNull]) :=
        List.rel_append (hok.fields hf he hx htt)
          (.cons ⟨(List.getElem?_eq_some_iff.mp he).1, rfl⟩ .nil)
      exact vals_br (values_sub hvs hsub) hl _ _

/-- `catch_all l`: a branch to `l`, which takes no values. -/
theorem catchAll {s : Store} {C : Context} {n a l : Nat} {cs : List Catch} {a₀ b : List OpType}
    (h : ASeqT s C [.handler n (.all l :: cs) (throwing a)] ⟨a₀, b⟩) :
    ASeqT s C [.plain (.br l)] ⟨a₀, b⟩ := by
  apply h.replace_fixed (vs := [])
  · intro x' y hi
    cases hi; rfl
  · intro x' y hi _
    cases hi with | handler hcs hb =>
      exact vals_br (vs := []) .nil (hcs _ (List.mem_cons_self ..)) _ _

/-- `catch_all_ref l`: the exception's reference, then a branch to `l`. -/
theorem catchAllRef {s : Store} {C : Context} {n a l : Nat} {cs : List Catch}
    {a₀ b : List OpType} (h : ASeqT s C [.handler n (.allRef l :: cs) (throwing a)] ⟨a₀, b⟩) :
    ASeqT s C [.refExnAddr a, .plain (.br l)] ⟨a₀, b⟩ := by
  apply h.replace_fixed (vs := [])
  · intro x' y hi
    cases hi; rfl
  · intro x' y hi _
    cases hi with | handler hcs hb =>
      obtain ⟨lts, hl, hsub⟩ := hcs _ (List.mem_cons_self ..)
      have ha := throwing_addr (pre := []) (post := []) (by simpa using hb)
      have hv : List.Forall₂ (Val.HasType s) [.ref (.exn a)] [exnNonNull] := .cons ⟨ha, rfl⟩ .nil
      exact vals_br (values_sub hv hsub) hl _ _

/-- A clause that does not take the exception leaves the remaining clauses. -/
theorem handlerNext {s : Store} {C : Context} {n a : Nat} {c : Catch} {cs : List Catch}
    {a₀ b : List OpType} (h : ASeqT s C [.handler n (c :: cs) (throwing a)] ⟨a₀, b⟩) :
    ASeqT s C [.handler n cs (throwing a)] ⟨a₀, b⟩ := by
  obtain ⟨p, x, y, z, hin, hout, hm, hi⟩ := ASeqT.single_iff.mp h
  cases hi with | handler hcs hb =>
    exact ASeqT.single_iff.mpr ⟨p, x, _, _, hin, hout, hm,
      .handler (fun c' h' => hcs c' (List.mem_cons_of_mem _ h')) hb⟩

end ASeqT

theorem block_returnInvoke_args {s : Store} {C : Context} {vs : List Val} {k a : Nat}
    (L : BlockCtx k) {a₀ b : List OpType} {fn : FuncInst} {ft : FuncType} {ts : List ValType}
    (h : ASeqT s C (L.fill (vals vs ++ [.returnInvoke a])) ⟨a₀, b⟩)
    (hr : C.return_ = some ts) (hfn : s.funcs[a]? = some fn) (hft : fn.type.expand = some ft)
    (hlen : vs.length = ft.params.length) :
    List.Forall₂ (Val.HasType s) vs ft.params ∧ ResultSub ft.results ts := by
  induction L generalizing C a₀ b with
  | base preValues rest =>
    obtain ⟨x, y, he⟩ := h.fragment_vals
    exact he.returnInvoke_args hr hfn hft hlen
  | label preValues n cont inner rest ih =>
    obtain ⟨x, y, he⟩ := h.fragment_vals
    obtain ⟨p, x, y, z, hin, hout, hm, hi⟩ := ASeqT.single_iff.mp he
    cases hi with | label hn hc hb => exact ih hb hr
  | handler preValues n cs inner rest ih =>
    obtain ⟨x, y, he⟩ := h.fragment_vals
    obtain ⟨p, x, y, z, hin, hout, hm, hi⟩ := ASeqT.single_iff.mp he
    cases hi with | handler hcs hb => exact ih hb hr

/-- `return_invoke` leaves the frame: the arguments, then the callee's invocation, whose results
match the frame's return type. -/
theorem ASeqT.returnInvoke {s : Store} {C : Context} {n k a : Nat} {f : Frame}
    {fn : FuncInst} {ft : FuncType} {vs : List Val} {a₀ b : List OpType} (L : BlockCtx k)
    (h : ASeqT s C [.frame n f (L.fill (vals vs ++ [.returnInvoke a]))] ⟨a₀, b⟩)
    (hfn : s.funcs[a]? = some fn) (hft : fn.type.expand = some ft)
    (hlen : vs.length = ft.params.length) : ASeqT s C (vals vs ++ [.invoke a]) ⟨a₀, b⟩ := by
  apply h.replace_fixed (vs := [])
  · intro x y hi
    cases hi; rfl
  · intro x y hi _
    cases hi with | frame hn hf hb =>
      obtain ⟨hvs, hsub⟩ := block_returnInvoke_args L hb rfl hfn hft hlen
      exact .sub ((ASeqT.values hvs).append_pure (.single (.invoke hfn hft))
        (ASeqT.vals_sets' vs) (ASeqT.vals_dead' vs)) (Matches.of_sub hsub)

end FVA.Wasm.Valid
