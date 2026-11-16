import FVA.Proof.Valid.Exception

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

/-- Pending control transfers stay explicit until their enclosing label or frame handles them. -/
inductive FragmentProgress (H : HostSem) (s : Store) (f : Frame) (C : Context) :
    List AInstr → Prop where
  | values (vs : List Val) : FragmentProgress H s f C (vals vs)
  | trap : FragmentProgress H s f C [.trap]
  | branch {k j : Nat} {vs : List Val} {ts : List ValType} (L : BlockCtx k)
      (ht : C.labels[j]? = some ts) (hlen : vs.length = ts.length) :
      FragmentProgress H s f C (L.fill (vals vs ++ [.plain (.br (k + j))]))
  | return_ {k : Nat} {vs : List Val} {ts : List ValType} (L : BlockCtx k)
      (ht : C.return_ = some ts) (hlen : vs.length = ts.length) :
      FragmentProgress H s f C (L.fill (vals vs ++ [.plain .return_]))
  | returnInvoke {k a : Nat} {vs : List Val} {ts : List ValType} {fn : FuncInst}
      {ft : FuncType} (L : BlockCtx k) (ht : C.return_ = some ts)
      (hfn : s.funcs[a]? = some fn) (hft : fn.type.expand = some ft)
      (hlen : vs.length = ft.params.length) :
      FragmentProgress H s f C (L.fill (vals vs ++ [.returnInvoke a]))
  /-- An exception in flight, unwound to the fragment's top. -/
  | throwing (a : Nat) : FragmentProgress H s f C (throwing a)
  | step {es : List AInstr} {c' : Config} (h : Step H ⟨s, f, es⟩ c') :
      FragmentProgress H s f C es

/-- Extend the outer block context without changing its branch depth. -/
def surround {k : Nat} (L : BlockCtx k) (pre : List Val) (post : List AInstr) : BlockCtx k :=
  match L with
  | .base vs rest => .base (pre ++ vs) (rest ++ post)
  | .label vs n cont inner rest => .label (pre ++ vs) n cont inner (rest ++ post)
  | .handler vs n cs inner rest => .handler (pre ++ vs) n cs inner (rest ++ post)

theorem surround_fill {k : Nat} (L : BlockCtx k) (pre : List Val) (post es : List AInstr) :
    (surround L pre post).fill es = vals pre ++ L.fill es ++ post := by
  cases L <;> simp only [surround, BlockCtx.fill, List.map_append, List.append_assoc]

theorem FragmentProgress.prepend {H : HostSem} {s : Store} {f : Frame} {C : Context}
    {es : List AInstr} (h : FragmentProgress H s f C es) (pre : List Val) :
    FragmentProgress H s f C (vals pre ++ es) := by
  cases h with
  | values vs =>
    simpa only [List.map_append] using FragmentProgress.values (H := H)
      (s := s) (f := f) (C := C) (pre ++ vs)
  | trap =>
    by_cases hp : pre = []
    · subst pre; exact .trap
    · have hne : (EvalCtx.seq pre .hole []).fill [.trap] ≠ [.trap] := by
        intro he
        have hn := congrArg List.length he
        simp only [EvalCtx.fill, List.length_append, List.length_map, List.length_singleton,
          List.length_nil, Nat.add_zero] at hn
        exact hp (List.length_eq_zero_iff.mp (by omega))
      simpa only [EvalCtx.fill, List.append_nil] using
        FragmentProgress.step (C := C) (StepP.trap (H := H) (s := s) (f := f)
          (.seq pre .hole []) hne)
  | branch L ht hlen =>
    simpa only [surround_fill, List.append_nil] using
      FragmentProgress.branch (H := H) (s := s) (f := f) (surround L pre []) ht hlen
  | return_ L ht hlen =>
    simpa only [surround_fill, List.append_nil] using
      FragmentProgress.return_ (H := H) (s := s) (f := f) (surround L pre []) ht hlen
  | returnInvoke L ht hfn hft hlen =>
    simpa only [surround_fill, List.append_nil] using
      FragmentProgress.returnInvoke (H := H) (s := s) (f := f) (surround L pre []) ht hfn hft hlen
  | throwing a =>
    by_cases hp : pre = []
    · subst pre; exact .throwing a
    · simpa only [List.append_nil] using FragmentProgress.step (C := C)
        (StepP.throwRefInstrs (H := H) (s := s) (f := f) (a := a) (vs := pre) (rest := [])
          (.inl hp))
  | step hs =>
    simpa only [List.append_nil] using FragmentProgress.step (C := C)
      (StepP.seq (vs := pre) (rest := []) hs)

theorem FragmentProgress.append_or_values {H : HostSem} {s : Store} {f : Frame}
    {C : Context} {es : List AInstr} (h : FragmentProgress H s f C es)
    (post : List AInstr) : (∃ vs, es = vals vs) ∨ FragmentProgress H s f C (es ++ post) := by
  cases h with
  | values vs => exact .inl ⟨vs, rfl⟩
  | trap =>
    right
    by_cases hp : post = []
    · subst post; exact .trap
    · apply FragmentProgress.step (StepP.trap (.seq [] .hole post) ?_)
      intro he
      have hn := congrArg List.length he
      simp only [EvalCtx.fill, List.map_nil, List.length_append,
        List.length_singleton, List.length_nil, Nat.zero_add] at hn
      exact hp (List.length_eq_zero_iff.mp (by omega))
  | branch L ht hlen =>
    right
    simpa only [surround_fill, List.map_nil, List.nil_append] using
      FragmentProgress.branch (H := H) (s := s) (f := f) (surround L [] post) ht hlen
  | return_ L ht hlen =>
    right
    simpa only [surround_fill, List.map_nil, List.nil_append] using
      FragmentProgress.return_ (H := H) (s := s) (f := f) (surround L [] post) ht hlen
  | returnInvoke L ht hfn hft hlen =>
    right
    simpa only [surround_fill, List.map_nil, List.nil_append] using
      FragmentProgress.returnInvoke (H := H) (s := s) (f := f) (surround L [] post) ht hfn hft
        hlen
  | throwing a =>
    right
    by_cases hp : post = []
    · subst post; simpa only [List.append_nil] using FragmentProgress.throwing a
    · simpa only [List.map_nil, List.nil_append] using FragmentProgress.step (C := C)
        (StepP.throwRefInstrs (H := H) (s := s) (f := f) (a := a) (vs := []) (rest := post)
          (.inr hp))
  | step hs =>
    right
    exact .step (.seq (vs := []) (rest := post) hs)

theorem typed_matches {s : Store} {vs : List Val} {a b : List OpType}
    (h : List.Forall₂ (HasOpType s) vs a) (hm : Matches a b) :
    List.Forall₂ (HasOpType s) vs b := by
  induction h generalizing b with
  | nil => cases hm; exact .nil
  | @cons v t vs ts hv hs ih =>
    cases hm with | @cons _ u _ _ ht hts =>
      cases t with
      | bot | refBot => cases hv
      | val t =>
        cases u with
        | bot | refBot => cases ht
        | val u => exact .cons (Val.HasType.sub hv ht) (ih hts)

theorem typed_split {s : Store} {vs : List Val} {a b : List OpType}
    (h : List.Forall₂ (HasOpType s) vs (a ++ b)) :
    ∃ pre args, vs = pre ++ args ∧ List.Forall₂ (HasOpType s) pre a ∧
      List.Forall₂ (HasOpType s) args b :=
  ⟨vs.take a.length, vs.drop a.length, (List.take_append_drop ..).symm,
    List.forall₂_take_append _ _ _ h, List.forall₂_drop_append _ _ _ h⟩

theorem ASeqT.values_op {s : Store} {C : Context} {vs : List Val} {ts : List OpType}
    (h : List.Forall₂ (HasOpType s) vs ts) : ASeqT s C (vals vs) ⟨[], ts⟩ := by
  induction h with
  | nil => exact .nil
  | @cons v t vs ts hv hs ih =>
    simpa only [List.append_nil, List.singleton_append, List.map_cons] using
      (ASeqT.hasOp_value hv).append_pure (ih.frame [t]) (by simp [↓Val.instr_sets'])
        (by simp [↓Val.instr_dead'])

theorem ASeqT.values_typed {s : Store} {C : Context} {vs : List Val} {ts : List OpType}
    (h : ASeqT s C (vals vs) ⟨[], ts⟩) : List.Forall₂ (HasOpType s) vs ts := by
  obtain ⟨vts, hm, hv⟩ := h.values_inv
  exact typed_matches (hasOp_ops hv) hm

/-- The last instruction of a sequence is typed after its prefix (`C.after es`); it is the
redex only once the prefix has reduced to values, which leave the context unchanged. -/
theorem progress_snoc {H : HostSem} {s : Store} {f : Frame} {C : Context}
    {vs : List Val} {es : List AInstr} {e : AInstr} {a p x y : List OpType}
    (hf : FrameCtx s f C) (hs : ASeqT s C es ⟨a, p ++ x⟩) (hm : Matches x y)
    (hvs : List.Forall₂ (HasOpType s) vs a)
    (hp : FragmentProgress H s f C (vals vs ++ es))
    (hi : FrameCtx s f (C.after es) → ∀ args, List.Forall₂ (HasOpType s) args y →
      FragmentProgress H s f (C.after es) (vals args ++ [e])) :
    FragmentProgress H s f C (vals vs ++ (es ++ [e])) := by
  rcases hp.append_or_values [e] with ⟨ws, heq⟩ | hp'
  · have hes : es = vals (ws.drop vs.length) := by
      have h1 : (vals vs ++ es).drop vs.length = es := List.drop_left' (by simp)
      rw [heq] at h1
      rw [← h1]
      simp
    have hC : C.after es = C := by
      rw [hes]
      exact ASeqT.after_pure C (ASeqT.vals_sets' _) (ASeqT.vals_dead' _)
    rw [hC] at hi
    have hi := hi hf
    have hws : ASeqT s C (vals ws) ⟨[], p ++ x⟩ := by
      rw [← heq]
      exact (ASeqT.values_op hvs).append_pure hs (ASeqT.vals_sets' vs) (ASeqT.vals_dead' vs)
    have hargs := typed_matches hws.values_typed ((Matches.refl p).append hm)
    obtain ⟨pre, args, hsplit, _, harg⟩ := typed_split hargs
    rw [← List.append_assoc, heq, hsplit]
    simpa only [List.map_append, List.append_assoc] using (hi args harg).prepend pre
  · simpa only [List.append_assoc] using hp'

end FVA.Wasm.Valid
