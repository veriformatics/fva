import FVA.Proof.Valid.Control

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

theorem ASeqT.fragment {s : Store} {C : Context} {pre es post : List AInstr}
    {a b : List OpType} (h : ASeqT s C (pre ++ es ++ post) ⟨a, b⟩) :
    ∃ x y, ASeqT s C es ⟨x, y⟩ := by
  obtain ⟨y, hpre, _⟩ := h.split (xs := pre ++ es) (ys := post)
  obtain ⟨x, _, he⟩ := hpre.split (xs := pre) (ys := es)
  exact ⟨x, y, he⟩

/-- A sequence holding an administrative instruction without a typing rule is not well typed (the
P′ forms, typed from U28c). -/
theorem ASeqT.not_mem {s : Store} {C : Context} {es : List AInstr} {e : AInstr}
    {a b : List OpType} (hmem : e ∈ es) (he : ∀ C x y, ¬ AInstrT s C e ⟨x, y⟩) :
    ¬ ASeqT s C es ⟨a, b⟩ := by
  intro h
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hmem
  have h' : ASeqT s C (pre ++ [e] ++ post) ⟨a, b⟩ := by
    simpa only [List.append_assoc, List.singleton_append] using h
  obtain ⟨x, y, hx⟩ := h'.fragment
  obtain ⟨p, x', y', z, -, -, -, hi⟩ :=
    ASeqT.snoc_iff.mp (show ASeqT s C ([] ++ [e]) ⟨x, y⟩ from hx)
  exact he _ _ _ hi

/-- A plain instruction without a 2.0 typing rule. -/
theorem AInstrT.not_plain {s : Store} {i : Instr} (hi : ∀ C st, ¬ InstrT C i st) :
    ∀ C x y, ¬ AInstrT s C (.plain i) ⟨x, y⟩ := by
  intro C x y h
  cases h with | plain h => exact hi _ _ h

theorem ASeqT.br_args {s : Store} {C : Context} {vs : List Val} {l : Nat}
    {a b : List OpType} {ts : List ValType}
    (h : ASeqT s C (vals vs ++ [.plain (.br l)]) ⟨a, b⟩)
    (ht : C.labels[l]? = some ts) (hlen : vs.length = ts.length) :
    List.Forall₂ (Val.HasType s) vs ts := by
  obtain ⟨p, x, y, z, hout, hs, hm, hi⟩ := ASeqT.snoc_iff.mp h
  cases hi with | plain hi =>
    cases hi with | @br _ _ ts' t₁ t₂ hb =>
      have heq := Option.some.inj (hb.symm.trans ht)
      subst ts'
      obtain ⟨vts, hv, hvs⟩ := hs.values_inv
      have hh : Matches (a ++ ops vts) ((p ++ t₁) ++ ops ts) := by
        simpa only [List.append_assoc] using hv.trans ((Matches.refl p).append hm)
      have hlen' : (ops vts).length = (ops ts).length := by
        simp only [ops, List.length_map]
        exact hvs.length_eq.symm.trans hlen
      have htypes := (hh.append_inv hlen').2.ops_eq
      subst vts
      exact hvs

theorem ASeqT.return_args {s : Store} {C : Context} {vs : List Val}
    {a b : List OpType} {ts : List ValType}
    (h : ASeqT s C (vals vs ++ [.plain .return_]) ⟨a, b⟩)
    (ht : C.return_ = some ts) (hlen : vs.length = ts.length) :
    List.Forall₂ (Val.HasType s) vs ts := by
  obtain ⟨p, x, y, z, hout, hs, hm, hi⟩ := ASeqT.snoc_iff.mp h
  cases hi with | plain hi =>
    cases hi with | @return_ _ ts' t₁ t₂ hb =>
      have heq := Option.some.inj (hb.symm.trans ht)
      subst ts'
      obtain ⟨vts, hv, hvs⟩ := hs.values_inv
      have hh : Matches (a ++ ops vts) ((p ++ t₁) ++ ops ts) := by
        simpa only [List.append_assoc] using hv.trans ((Matches.refl p).append hm)
      have hlen' : (ops vts).length = (ops ts).length := by
        simp only [ops, List.length_map]
        exact hvs.length_eq.symm.trans hlen
      have htypes := (hh.append_inv hlen').2.ops_eq
      subst vts
      exact hvs

theorem block_br_args {s : Store} {C : Context} {vs : List Val} {k j : Nat}
    (L : BlockCtx k) {a b : List OpType} {ts : List ValType}
    (h : ASeqT s C (L.fill (vals vs ++ [.plain (.br (k + j))])) ⟨a, b⟩)
    (ht : C.labels[j]? = some ts) (hlen : vs.length = ts.length) :
    List.Forall₂ (Val.HasType s) vs ts := by
  induction L generalizing C a b j with
  | base preValues rest =>
    obtain ⟨x, y, he⟩ := h.fragment
    exact he.br_args (by simpa only [Nat.zero_add] using ht) hlen
  | @label k preValues n cont inner rest ih =>
    obtain ⟨x, y, he⟩ := h.fragment
    obtain ⟨p, x, y, z, hin, hout, hm, hi⟩ := ASeqT.single_iff.mp he
    cases hi with | label hn hc hb =>
      have heq : k + 1 + j = k + (j + 1) := by omega
      rw [heq] at hb
      exact ih hb ht
  | handler preValues n cs inner rest ih =>
    obtain ⟨x, y, he⟩ := h.fragment
    obtain ⟨p, x, y, z, hin, hout, hm, hi⟩ := ASeqT.single_iff.mp he
    cases hi

theorem block_return_args {s : Store} {C : Context} {vs : List Val} {k : Nat}
    (L : BlockCtx k) {a b : List OpType} {ts : List ValType}
    (h : ASeqT s C (L.fill (vals vs ++ [.plain .return_])) ⟨a, b⟩)
    (ht : C.return_ = some ts) (hlen : vs.length = ts.length) :
    List.Forall₂ (Val.HasType s) vs ts := by
  induction L generalizing C a b with
  | base preValues rest =>
    obtain ⟨x, y, he⟩ := h.fragment
    exact he.return_args ht hlen
  | label preValues n cont inner rest ih =>
    obtain ⟨x, y, he⟩ := h.fragment
    obtain ⟨p, x, y, z, hin, hout, hm, hi⟩ := ASeqT.single_iff.mp he
    cases hi with | label hn hc hb => exact ih hb ht
  | handler preValues n cs inner rest ih =>
    obtain ⟨x, y, he⟩ := h.fragment
    obtain ⟨p, x, y, z, hin, hout, hm, hi⟩ := ASeqT.single_iff.mp he
    cases hi

/-- The hole of a block context holds a sequence typed in some context. -/
theorem ASeqT.fill_inner {s : Store} {C : Context} {k : Nat} (L : BlockCtx k) {es : List AInstr}
    {a b : List OpType} (h : ASeqT s C (L.fill es) ⟨a, b⟩) : ∃ C' x y, ASeqT s C' es ⟨x, y⟩ := by
  induction L generalizing C a b with
  | base preValues rest =>
    obtain ⟨x, y, he⟩ := h.fragment
    exact ⟨C, x, y, he⟩
  | label preValues n cont inner rest ih =>
    obtain ⟨x, y, he⟩ := h.fragment
    obtain ⟨p, x, y, z, hin, hout, hm, hi⟩ := ASeqT.single_iff.mp he
    cases hi with | label hn hc hb => exact ih hb
  | handler preValues n cs inner rest ih =>
    obtain ⟨x, y, he⟩ := h.fragment
    obtain ⟨p, x, y, z, hin, hout, hm, hi⟩ := ASeqT.single_iff.mp he
    cases hi

theorem ASeqT.labelExit {s : Store} {C : Context} {n : Nat} {cont : List Instr}
    {vs : List Val} {a b : List OpType}
    (h : ASeqT s C [.label n cont (vals vs)] ⟨a, b⟩) : ASeqT s C (vals vs) ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [])
  · intro x y hi
    cases hi; rfl
  · intro x y hi _
    cases hi with | label hn hc hb =>
      obtain ⟨ts, hm, hvs⟩ := hb.values_inv
      exact .sub (.values hvs) hm

theorem ASeqT.frameExit {s : Store} {C : Context} {n : Nat} {f : Frame}
    {vs : List Val} {a b : List OpType}
    (h : ASeqT s C [.frame n f (vals vs)] ⟨a, b⟩) : ASeqT s C (vals vs) ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [])
  · intro x y hi
    cases hi; rfl
  · intro x y hi _
    cases hi with | frame hn hf hb =>
      obtain ⟨ts, hm, hvs⟩ := hb.values_inv
      exact .sub (.values hvs) hm

theorem ASeqT.br {s : Store} {C : Context} {n l : Nat} {cont : List Instr}
    {vs : List Val} {a b : List OpType} (L : BlockCtx l)
    (h : ASeqT s C [.label n cont (L.fill (vals vs ++ [.plain (.br l)]))] ⟨a, b⟩)
    (hlen : vs.length = n) : ASeqT s C (vals vs ++ cont.map .plain) ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [])
  · intro x y hi
    cases hi; rfl
  · intro x y hi _
    cases hi with | label hn hc hb =>
      have hvs := block_br_args (j := 0) L hb rfl (hlen.trans hn.symm)
      exact (ASeqT.values hvs).append (ASeqT.plain hc)

theorem ASeqT.return_ {s : Store} {C : Context} {n k : Nat} {f : Frame}
    {vs : List Val} {a b : List OpType} (L : BlockCtx k)
    (h : ASeqT s C [.frame n f (L.fill (vals vs ++ [.plain .return_]))] ⟨a, b⟩)
    (hlen : vs.length = n) : ASeqT s C (vals vs) ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [])
  · intro x y hi
    cases hi; rfl
  · intro x y hi _
    cases hi with | frame hn hf hb =>
      have hvs := block_return_args L hb rfl (hlen.trans hn.symm)
      exact ASeqT.values hvs

end FVA.Wasm.Valid
