import FVA.Proof.Valid.ProgressInstr

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

/-- A handler around an exception in flight: the first clause takes it or passes it on. -/
theorem handler_throwing_progress {H : HostSem} {s : Store} {f : Frame} {C : Context}
    {n a : Nat} (cs : List Catch) : FragmentProgress H s f C [.handler n cs (throwing a)] := by
  cases cs with
  | nil => exact .step .throwRefHandlerEmpty
  | cons c cs =>
    by_cases hc : c.Catches s f a
    · cases c with
      | tag x l => obtain ⟨e, he, hx⟩ := hc; exact .step (.throwRefCatch he hx)
      | tagRef x l => obtain ⟨e, he, hx⟩ := hc; exact .step (.throwRefCatchRef he hx)
      | all l => exact .step .throwRefCatchAll
      | allRef l => exact .step .throwRefCatchAllRef
    · exact .step (.throwRefHandlerNext hc)

theorem ASeqT.values_length {s : Store} {C : Context} {vs : List Val} {ts : List ValType}
    (h : ASeqT s C (vals vs) ⟨[], ops ts⟩) : vs.length = ts.length := by
  simpa only [ops, List.length_map] using h.values_typed.length_eq

set_option maxHeartbeats 1000000 in
theorem ainstr_progress {H : HostSem} (hH : ValidHost H) {s : Store} {C : Context}
    {i : AInstr} {st : StackType} (hi : AInstrT s C i st) :
    ∀ (f : Frame) (args : List Val), FrameCtx s f C →
      List.Forall₂ (HasOpType s) args st.ins →
        FragmentProgress H s f C (vals args ++ [i]) := by
  induction hi using AInstrT.rec
    (motive_2 := fun C es st _ => ∀ (f : Frame) (args : List Val), FrameCtx s f C →
      List.Forall₂ (HasOpType s) args st.ins →
        FragmentProgress H s f C (vals args ++ es))
  all_goals try intro f args hf hargs
  case plain hi => exact instr_progress hi hf hargs
  case refFuncAddr ha => cases hargs; exact .values [.ref (.func _)]
  case refExternAddr => cases hargs; exact .values [.ref (.extern _)]
  case refNullAddr => cases hargs; exact .values [.ref .null]
  case refExnAddr => cases hargs; exact .values [.ref (.exn _)]
  case trap => exact FragmentProgress.trap.prepend args
  case invoke C addr fi ft hfi hft =>
    have hvs := hasOp_ops_iff.mp hargs
    have hlen := hvs.length_eq
    cases fi with
    | wasm dt inst code => exact .step (.invoke hfi hft hlen)
    | host dt id =>
      obtain ⟨out, hout⟩ := (hH _ _ _ _ _ _ hfi hft hvs).1
      cases out with
      | returned s' res => exact .step (.invokeHost hfi hft hlen hout)
      | trapped s' => exact .step (.invokeHostTrap hfi hft hlen hout)
      | diverged => exact .step (.invokeHostDiverge hfi hft hlen hout)
  case label C n cont body t₁ t₂ hn hc hb ih =>
    cases hargs
    have hp := ih f [] (hf.withLabel t₁) .nil
    simp only [List.map_nil, List.nil_append] at hp
    cases hp with
    | values vs => exact .step .labelExit
    | trap => exact .step (StepP.trap (.label n cont .hole) (by simp [EvalCtx.fill]))
    | @branch k j vs ts L ht hlen =>
      cases j with
      | zero =>
        have heq : t₁ = ts := Option.some.inj ht
        subst ts
        exact .step (.br L (hlen.trans hn))
      | succ j =>
        have heq : k + 1 + j = k + (j + 1) := by omega
        simpa only [BlockCtx.fill, List.map_nil, List.nil_append, List.append_nil, heq] using
          FragmentProgress.branch (H := H) (s := s) (f := f) (C := C)
            (BlockCtx.label [] n cont L []) ht hlen
    | @return_ k vs ts L ht hlen =>
      simpa only [BlockCtx.fill, List.map_nil, List.nil_append, List.append_nil] using
        FragmentProgress.return_ (H := H) (s := s) (f := f) (C := C)
          (BlockCtx.label [] n cont L []) ht hlen
    | returnInvoke L ht hfn hft hlen =>
      simpa only [BlockCtx.fill, List.map_nil, List.nil_append, List.append_nil] using
        FragmentProgress.returnInvoke (H := H) (s := s) (f := f) (C := C)
          (BlockCtx.label [] n cont L []) ht hfn hft hlen
    | throwing a => exact .step .throwRefLabel
    | step hs => exact .step (.label hs)
  case frame C Cinner n fi body ts hn hinner hb ih =>
    cases hargs
    have hp := ih fi [] (hinner.ctx.withReturn (some ts)) .nil
    simp only [List.map_nil, List.nil_append] at hp
    cases hp with
    | values vs => exact .step (.frameExit (hb.values_length.trans hn))
    | trap => exact .step .trapFrame
    | @branch k j vs rts L ht hlen =>
      change Cinner.labels[j]? = some rts at ht
      rw [hinner.noLabels] at ht
      simp at ht
    | @return_ k vs rts L ht hlen =>
      have heq : ts = rts := Option.some.inj ht
      subst rts
      exact .step (.return_ L (hlen.trans hn))
    | returnInvoke L ht hfn hft hlen => exact .step (.returnInvoke L hfn hft hlen)
    | throwing a => exact .step .throwRefFrame
    | step hs => exact .step (.frame hs)
  case handler C n cs body ts hcs hb ih =>
    cases hargs
    have hp := ih f [] hf .nil
    simp only [List.map_nil, List.nil_append] at hp
    cases hp with
    | values vs => exact .step .handlerExit
    | trap => exact .step (StepP.trap (.handler n cs .hole) (by simp [EvalCtx.fill]))
    | branch L ht hlen =>
      simpa only [BlockCtx.fill, List.map_nil, List.nil_append, List.append_nil] using
        FragmentProgress.branch (H := H) (s := s) (f := f) (C := C)
          (BlockCtx.handler [] n cs L []) ht hlen
    | return_ L ht hlen =>
      simpa only [BlockCtx.fill, List.map_nil, List.nil_append, List.append_nil] using
        FragmentProgress.return_ (H := H) (s := s) (f := f) (C := C)
          (BlockCtx.handler [] n cs L []) ht hlen
    | returnInvoke L ht hfn hft hlen =>
      simpa only [BlockCtx.fill, List.map_nil, List.nil_append, List.append_nil] using
        FragmentProgress.returnInvoke (H := H) (s := s) (f := f) (C := C)
          (BlockCtx.handler [] n cs L []) ht hfn hft hlen
    | throwing a => exact handler_throwing_progress cs
    | step hs => exact .step (.handler hs)
  case returnInvoke C a fi ft rs t₃ t₄ hfi hft hr hs =>
    obtain ⟨pre, args, rfl, _, hlast⟩ := typed_split hargs
    have hl : args.length = ft.params.length := by
      simpa only [ops, List.length_map] using hlast.length_eq
    simpa only [BlockCtx.fill, List.map_append, List.append_assoc, List.append_nil] using
      FragmentProgress.returnInvoke (H := H) (s := s) (f := f) (C := C)
        (BlockCtx.base pre []) hr hfi hft hl
  case nil =>
    rename_i f args hf hargs
    simpa only [List.append_nil] using FragmentProgress.values (H := H)
      (s := s) (f := f) (C := _) args
  case snoc hs hm hi ihs ihi f args hf hargs =>
    exact progress_snoc hf hs hm hargs (ihs f args hf hargs) (fun hf' vs hvs => ihi f vs hf' hvs)
  case sub hs hm ih f args hf hargs => exact ih f args hf hargs

theorem aseq_progress {H : HostSem} (hH : ValidHost H) {s : Store} {C : Context}
    {es : List AInstr} {a b : List OpType} (hs : ASeqT s C es ⟨a, b⟩) (f : Frame)
    (args : List Val) (hf : FrameCtx s f C) (hargs : List.Forall₂ (HasOpType s) args a) :
    FragmentProgress H s f C (vals args ++ es) := by
  induction es using List.reverseRecOn generalizing b with
  | nil =>
    simpa only [List.append_nil] using FragmentProgress.values (H := H)
      (s := s) (f := f) (C := C) args
  | append_singleton es e ih =>
    obtain ⟨p, x, y, z, hout, hpre, hm, hi⟩ := ASeqT.snoc_iff.mp hs
    exact progress_snoc hf hpre hm hargs (ih hpre)
      (fun hf' vs hvs => ainstr_progress hH hi f vs hf' hvs)

theorem progress : Progress := by
  intro H c ts hH hok
  obtain ⟨s, f, es⟩ := c
  obtain ⟨hstore, C, hf, ht⟩ := hok
  have hp := aseq_progress hH ht f [] hf.ctx .nil
  simp only [List.map_nil, List.nil_append] at hp
  cases hp with
  | values vs => exact .inl ⟨.returned s vs, rfl, rfl⟩
  | trap => exact .inl ⟨.trapped s, rfl, rfl⟩
  | @branch k j vs rts L hlabel hlen =>
    rw [hf.noLabels] at hlabel
    simp at hlabel
  | @return_ k vs rts L hret hlen =>
    rw [hf.noReturn] at hret
    cases hret
  | returnInvoke L hret hfn hft hlen =>
    rw [hf.noReturn] at hret
    cases hret
  | throwing a => exact .inl ⟨.thrown s a, rfl, rfl⟩
  | step hs => exact .inr ⟨_, hs⟩

end FVA.Wasm.Valid
