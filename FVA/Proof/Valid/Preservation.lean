import FVA.Proof.Valid.Exception
import FVA.Proof.Valid.Memory
import FVA.Proof.Valid.Variables

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

/-- `C.after es = C` for a redex of values and instructions that neither initialize a local
nor end the sequence. -/
macro (name := pureAfter) "pure_after" : tactic => `(tactic| exact ASeqT.after_pure _
  (by simp [↓ASeqT.vals_sets', ↓Val.instr_sets', AInstr.sets, Instr.sets, throwing])
  (by simp [↓ASeqT.vals_dead', ↓Val.instr_dead', AInstr.dead, throwing]))

/-- Fragment postcondition; context transport accounts for grown table/memory minima and for
locals the step initialized: the rest of the enclosing sequence was typed in the context after
the fragment (`ASeqT.snoc`, `Context.after`), which must still entail the one after its
successor (a dead end entails anything, contract X9). -/
def Preserved (s : Store) (C : Context) (es : List AInstr) (a b : List OpType) (c : Config) :
    Prop :=
  s.Extends c.store ∧ StoreOK c.store ∧ ∃ D, C.Entails D ∧ FrameCtx c.store c.frame D ∧
    ASeqT c.store D c.instrs ⟨a, b⟩ ∧ (C.after es).Entails (D.after c.instrs)

private theorem same {s : Store} {f : Frame} {C : Context} {es es' : List AInstr}
    {a b : List OpType} (hok : StoreOK s) (hf : FrameCtx s f C)
    (he : ASeqT s C es' ⟨a, b⟩) (hes : (C.after es).Entails (C.after es')) :
    Preserved s C es a b ⟨s, f, es'⟩ :=
  ⟨Store.Extends.refl s, hok, C, Context.Entails.refl C, hf, he, hes⟩

/-- A redex leaving its context unchanged after it (no initialization, no dead end). -/
private theorem same_pure {s : Store} {f : Frame} {C : Context} {es es' : List AInstr}
    {a b : List OpType} (hok : StoreOK s) (hf : FrameCtx s f C)
    (he : ASeqT s C es' ⟨a, b⟩) (hp : C.after es = C := by pure_after) :
    Preserved s C es a b ⟨s, f, es'⟩ :=
  same hok hf he (by rw [hp]; exact Context.Entails.to_after C es')

private theorem changed {s s' : Store} {f : Frame} {C : Context} {es es' : List AInstr}
    {a b : List OpType} (hs : s.Extends s' ∧ StoreOK s') (hf : FrameCtx s f C)
    (he : ASeqT s C es' ⟨a, b⟩) (hp : C.after es = C := by pure_after) :
    Preserved s C es a b ⟨s', f, es'⟩ := by
  obtain ⟨D, hf', hc⟩ := hf.extendStore hs.1
  exact ⟨hs.1, hs.2, D, hc, hf', he.transport hs.1 hc,
    by rw [hp]; exact hc.trans (Context.Entails.to_after D es')⟩

/-- A redex allocating in the store: its result is typed in the grown store alone. -/
private theorem grown {s s' : Store} {f : Frame} {C : Context} {es es' : List AInstr}
    {a b : List OpType} (hs : s.Extends s' ∧ StoreOK s') (hf : FrameCtx s f C)
    (he : ∀ D, C.Entails D → FrameCtx s' f D → ASeqT s' D es' ⟨a, b⟩)
    (hp : C.after es = C := by pure_after) : Preserved s C es a b ⟨s', f, es'⟩ := by
  obtain ⟨D, hf', hc⟩ := hf.extendStore hs.1
  exact ⟨hs.1, hs.2, D, hc, hf', he D hc hf',
    by rw [hp]; exact hc.trans (Context.Entails.to_after D es')⟩

theorem FrameCtx.withLabels {s : Store} {f : Frame} {C : Context} (hf : FrameCtx s f C)
    (labels : List (List ValType)) : FrameCtx s f { C with labels := labels } := by
  obtain ⟨C₀, ls, ret, h, rfl⟩ := hf
  exact ⟨C₀, labels, ret, h, rfl⟩

theorem FrameCtx.frameT {s : Store} {f : Frame} {C : Context} (hf : FrameCtx s f C) :
    FrameT s f { C with labels := [], return_ := none } := by
  obtain ⟨C₀, ls, ret, h, rfl⟩ := hf
  have he : ({ C₀ with labels := [], return_ := none } : Context) = C₀ := by
    rw [← h.noLabels, ← h.noReturn]
  exact he.symm ▸ h

set_option maxHeartbeats 2000000 in
theorem fragment_preservation {H : HostSem} (hH : TypeSoundHost H) {c c' : Config}
    (step : Step H c c') : ∀ (C : Context) (a b : List OpType),
      StoreOK c.store → FrameCtx c.store c.frame C → ASeqT c.store C c.instrs ⟨a, b⟩ →
        Preserved c.store C c.instrs a b c' := by
  induction step <;> intro C a b hok hf ht
  case num hr =>
    obtain ⟨hs, hd⟩ := numResults_pure hr
    exact same_pure hok hf (ht.numeric hr) (ASeqT.after_pure _
      (by simp [↓ASeqT.vals_sets', AInstr.sets, hs]) (by simp [↓ASeqT.vals_dead', hd]))
  case refNull => exact same_pure hok hf ht.refNull
  case refIsNull => exact same_pure hok hf ht.refIsNull
  case refFunc ha => exact same_pure hok hf (ht.refFunc hf ha)
  case drop => exact same_pure hok hf ht.drop
  case select => exact same_pure hok hf ht.select
  case localGet hv => exact same_pure hok hf (ht.localGet hf hv)
  case localSet hx =>
    obtain ⟨C', hf', hC', ht'⟩ := ht.localSet hf
    have hCC : C.Entails C' := (Context.Entails.to_addSets C _).trans hC'
    refine ⟨Store.Extends.refl _, hok, C', hCC, hf', ht'.transport (Store.Extends.refl _) hCC, ?_⟩
    rw [Context.after_nil, ASeqT.after_eq_addSets _ (by simp [↓Val.instr_dead', AInstr.dead])]
    simpa [↓Val.instr_sets', AInstr.sets, Instr.sets] using hC'
  case localTee =>
    refine same hok hf ht.localTee ?_
    rw [ASeqT.after_eq_addSets _ (by simp [↓Val.instr_dead', AInstr.dead]),
      ASeqT.after_eq_addSets _ (by simp [↓Val.instr_dead', AInstr.dead])]
    simp only [List.flatMap_cons, ↓Val.instr_sets', AInstr.sets, Instr.sets, List.flatMap_nil,
      List.nil_append, List.append_nil]
    exact Context.Entails.refl _
  case globalGet ha hg => exact same_pure hok hf (ht.globalGet hok hf ha hg)
  case globalSet ha hg =>
    obtain ⟨hmut, hv, hm⟩ := ht.globalSet hf ha hg
    exact changed (hok.setGlobal hg hmut hv) hf (ASeqT.nil_iff.mpr hm)
  case tableGet ha hti hr => exact same_pure hok hf (ht.tableGet hok hf ha hti hr)
  case tableGetTrap => exact same_pure hok hf (.single .trap)
  case tableSet ha hti hi =>
    obtain ⟨hv, hm⟩ := ht.tableSet hf ha hti
    exact changed (hok.writeTable hti _ hv) hf (ASeqT.nil_iff.mpr hm)
  case tableSetTrap => exact same_pure hok hf (.single .trap)
  case tableSize => exact same_pure hok hf (ht.tableSize _)
  case tableGrow ha hti hg =>
    have hv := ht.tableGrow_ref hf ha hti
    exact changed (hok.growTable hti hg hv) hf (ht.tableGrow _)
  case tableGrowFail => exact same_pure hok hf (ht.tableGrow _)
  case tableFillTrap => exact same_pure hok hf (.single .trap)
  case tableFillZero => exact same_pure hok hf ht.tableFillZero
  case tableFill => exact same_pure hok hf ht.tableFill
  case tableCopyTrap => exact same_pure hok hf (.single .trap)
  case tableCopyZero => exact same_pure hok hf ht.tableCopyZero
  case tableCopyUp => exact same_pure hok hf ht.tableCopyUp
  case tableCopyDown => exact same_pure hok hf ht.tableCopyDown
  case tableInitTrap => exact same_pure hok hf (.single .trap)
  case tableInitZero => exact same_pure hok hf ht.tableInitZero
  case tableInit ha hel hti hei hn hsrc hdst hr =>
    exact same_pure hok hf (ht.tableInit hok hf hel hei hr)
  case elemDrop ha hei => exact changed (hok.dropElem hei) hf (ASeqT.nil_iff.mpr ht.elemDrop)
  case load => exact same_pure hok hf (ht.load _)
  case loadTrap => exact same_pure hok hf (.single .trap)
  case loadPacked => exact same_pure hok hf (ht.loadPacked _)
  case loadPackedTrap => exact same_pure hok hf (.single .trap)
  case store ha hmem hv hbound =>
    exact changed (hok.writeMem hmem _ _ _) hf (ASeqT.nil_iff.mpr ht.store)
  case storeTrap => exact same_pure hok hf (.single .trap)
  case storePacked ha hmem hv hbound =>
    exact changed (hok.writeMem hmem _ _ _) hf (ASeqT.nil_iff.mpr ht.storePacked)
  case storePackedTrap => exact same_pure hok hf (.single .trap)
  case memorySize => exact same_pure hok hf (ht.memorySize _)
  case memoryGrow ha hmem hg => exact changed (hok.growMem hmem hg) hf (ht.memoryGrow _)
  case memoryGrowFail => exact same_pure hok hf (ht.memoryGrow _)
  case memoryFillTrap => exact same_pure hok hf (.single .trap)
  case memoryFillZero => exact same_pure hok hf ht.memoryFillZero
  case memoryFill => exact same_pure hok hf ht.memoryFill
  case memoryCopyTrap => exact same_pure hok hf (.single .trap)
  case memoryCopyZero => exact same_pure hok hf ht.memoryCopyZero
  case memoryCopyUp => exact same_pure hok hf ht.memoryCopyUp
  case memoryCopyDown => exact same_pure hok hf ht.memoryCopyDown
  case memoryInitTrap => exact same_pure hok hf (.single .trap)
  case memoryInitZero => exact same_pure hok hf ht.memoryInitZero
  case memoryInit => exact same_pure hok hf (ht.memoryInit _)
  case dataDrop ha hdi => exact changed (hok.dropData hdi) hf (ASeqT.nil_iff.mpr ht.dataDrop)
  case nop => exact same_pure hok hf ht.nop
  case unreachable => exact same_pure hok hf (.single .trap)
  case block hbt hlen => exact same_pure hok hf (ht.block hf hbt hlen)
  case loop hbt hlen => exact same_pure hok hf (ht.loop hf hbt hlen)
  case ifTrue => exact same_pure hok hf ht.ifTrue
  case ifFalse => exact same_pure hok hf ht.ifFalse
  case labelExit => exact same_pure hok hf ht.labelExit
  case br L hlen => exact same_pure hok hf (ht.br L hlen)
  case brIfTrue => exact same_pure hok hf ht.brIfTrue
  case brIfFalse => exact same_pure hok hf ht.brIfFalse
  case brTable => exact same_pure hok hf ht.brTable
  case return_ L hlen => exact same_pure hok hf (ht.return_ L hlen)
  case call ha => exact same_pure hok hf (ht.call hf ha)
  case callIndirect htarget => exact same_pure hok hf (ht.callIndirect hf htarget)
  case callIndirectTrap => exact same_pure hok hf (.single .trap)
  case invoke hfi hft hlen => exact same_pure hok hf (ht.invoke hok hfi hft hlen)
  case frameExit => exact same_pure hok hf ht.frameExit
  case invokeHost hfi hft hlen hh =>
    obtain ⟨p, hp, hout, hargs⟩ := ht.invoke_inv hfi hft hlen
    obtain ⟨he, hres⟩ := (hH.1 _ _ _ _ _ _ hfi hft hargs).2 _ hh
    have hok' := hH.2 _ _ _ _ _ _ _ hok hfi hft hargs hh
    obtain ⟨D, hf', hc⟩ := hf.extendStore he
    exact ⟨he, hok', D, hc, hf', .sub ((ASeqT.values hres p).input hp) hout,
      by rw [ASeqT.after_pure C (by simp [↓ASeqT.vals_sets', AInstr.sets])
          (by simp [↓ASeqT.vals_dead', AInstr.dead]),
        ASeqT.after_pure D (ASeqT.vals_sets' _) (ASeqT.vals_dead' _)]; exact hc⟩
  case invokeHostTrap hfi hft hlen hh =>
    obtain ⟨p, hp, hout, hargs⟩ := ht.invoke_inv hfi hft hlen
    have he := (hH.1 _ _ _ _ _ _ hfi hft hargs).2 _ hh
    have hok' := hH.2 _ _ _ _ _ _ _ hok hfi hft hargs hh
    exact changed ⟨he, hok'⟩ hf (.single .trap)
  case invokeHostDiverge => exact same_pure hok hf ht
  case seq step ih =>
    obtain ⟨q, hpre, hrest⟩ := ht.split
    obtain ⟨p, hvals, hin⟩ := hpre.split
    have hv : ∀ (E : Context) (vs : List Val), E.after (vals vs) = E :=
      fun E vs => ASeqT.after_pure E (ASeqT.vals_sets' vs) (ASeqT.vals_dead' vs)
    rw [hv] at hin
    obtain ⟨he, hok', D, hc, hf', hout, hcl⟩ := ih _ _ _ hok hf hin
    simp only [← ASeqT.after_after, hv] at hrest
    refine ⟨he, hok', D, hc, hf', ((hvals.transport he hc).append_pure hout).append ?_, ?_⟩
    · simpa only [← ASeqT.after_after, hv] using hrest.transport he hcl
    · simpa only [← ASeqT.after_after, hv] using hcl.after _
  case label step ih =>
    obtain ⟨p, x, y, z, hin, hout, hm, hi⟩ := ASeqT.single_iff.mp ht
    cases hi with | @label _ _ _ _ t₁ t₂ hn hc hb =>
      obtain ⟨he, hok', D', hc', hf', hb', -⟩ := ih _ _ _ hok (hf.withLabel t₁) hb
      let D : Context := { D' with labels := C.labels }
      have hCD : C.Entails D := { hc' with labels := rfl }
      have hDD : D.withLabel t₁ = D' := by
        change { D' with labels := t₁ :: C.labels } = D'
        have hl : t₁ :: C.labels = D'.labels := hc'.labels
        rw [hl]
      refine ⟨he, hok', D, hCD, hf'.withLabels C.labels, ASeqT.single_iff.mpr ?_,
        (by rw [ASeqT.after_pure C (by simp [AInstr.sets]) (by simp [AInstr.dead]),
          ASeqT.after_pure D (by simp [AInstr.sets]) (by simp [AInstr.dead])]; exact hCD)⟩
      exact ⟨p, x, _, _, hin, hout, hm,
        .label hn (hc.transport hCD) (hDD.symm ▸ hb')⟩
  case frame step ih =>
    obtain ⟨p, x, y, z, hin, hout, hm, hi⟩ := ASeqT.single_iff.mp ht
    cases hi with | @frame _ Cinner _ _ _ ts hn hinner hb =>
      obtain ⟨he, hok', D', hc', hf', hb', -⟩ :=
        ih _ _ _ hok (hinner.ctx.withReturn (some ts)) hb
      have hl : D'.labels = [] := hc'.labels.symm.trans hinner.noLabels
      have hr : D'.return_ = some ts := hc'.return_.symm
      have hDD : ({ { D' with labels := [], return_ := none } with
          return_ := some ts } : Context) = D' := by
        change { D' with labels := [], return_ := some ts } = D'
        rw [← hl, ← hr]
      obtain ⟨D, houter, hCD⟩ := hf.extendStore he
      refine ⟨he, hok', D, hCD, houter, ASeqT.single_iff.mpr ?_,
        (by rw [ASeqT.after_pure C (by simp [AInstr.sets]) (by simp [AInstr.dead]),
          ASeqT.after_pure D (by simp [AInstr.sets]) (by simp [AInstr.dead])]; exact hCD)⟩
      exact ⟨p, x, _, _, hin, hout, hm, .frame hn hf'.frameT (hDD.symm ▸ hb')⟩
  case trap =>
    exact same hok hf (.single .trap) (Context.Entails.to_dead_after _ _ (by simp [AInstr.dead]))
  case trapFrame =>
    exact same hok hf (.single .trap) (Context.Entails.to_dead_after _ _ (by simp [AInstr.dead]))
  -- the P′ forms have no 2.0 typing rule (U28c types them): their redexes are not well typed
  case throwRefHandlerEmpty =>
    obtain ⟨p, x, y, z, -, -, -, hi⟩ := ASeqT.single_iff.mp ht
    cases hi with | handler hcs hb =>
      exact same hok hf (ASeqT.throwing_typed
        (ASeqT.throwing_addr (pre := []) (post := []) (by simpa using hb)) _ _)
        (Context.Entails.to_dead_after _ _ (by simp [AInstr.dead]))
  case handlerExit => exact same_pure hok hf ht.handlerExit
  case handler step ih =>
    obtain ⟨p, x, y, z, hin, hout, hm, hi⟩ := ASeqT.single_iff.mp ht
    cases hi with | handler hcs hb =>
      obtain ⟨he, hok', D, hCD, hf', hb', -⟩ := ih _ _ _ hok hf hb
      refine ⟨he, hok', D, hCD, hf', ASeqT.single_iff.mpr
        ⟨p, x, _, _, hin, hout, hm, .handler (fun c h' => hCD.catchOK (hcs c h')) hb'⟩, ?_⟩
      rw [ASeqT.after_pure C (by simp [AInstr.sets]) (by simp [AInstr.dead]),
        ASeqT.after_pure D (by simp [AInstr.sets]) (by simp [AInstr.dead])]
      exact hCD
  case throwRefCatch he hx => exact same_pure hok hf (ht.catchTag hok hf he hx)
  case throwRefCatchRef he hx => exact same_pure hok hf (ht.catchTagRef hok hf he hx)
  case throwRefCatchAll => exact same_pure hok hf ht.catchAll
  case throwRefCatchAllRef => exact same_pure hok hf ht.catchAllRef
  case throwRefHandlerNext => exact same_pure hok hf ht.handlerNext
  case tryTable hbt hlen => exact same_pure hok hf (ht.tryTable hf hbt hlen)
  case throw hta hti hft hres hlen =>
    exact grown (ht.throw_store hok hf hta hti hft hres hlen) hf
      (fun _ _ _ => ASeqT.throwing_typed (by simp) _ _)
  case returnCall ha =>
    obtain ⟨p, x, y, z, hin, hout, hm, hi⟩ := ASeqT.single_iff.mp ht
    cases hi with | plain hi =>
      cases hi with | returnCall hft hr hs =>
        obtain ⟨a', fi, ha', hfi, he⟩ := hf.funcType hft
        have heq := Option.some.inj (ha'.symm.trans ha)
        subst heq
        exact same_pure hok hf (ASeqT.single_iff.mpr
          ⟨p, x, _, _, hin, hout, hm, .returnInvoke hfi he hr hs⟩)
  case throwRefNull | returnCallRefNull | returnCallIndirectTrap | callRefNull | refAsNonNullNull =>
    exact same hok hf (.single .trap) (Context.Entails.to_dead_after _ _ (by simp [AInstr.dead]))
  case refAsNonNull hr => exact same_pure hok hf (ht.refAsNonNull hr)
  case brOnNullValue hr =>
    refine same_pure hok hf (ht.retype_top fun hi => ?_)
    cases hi with | plain hi =>
      cases hi with | @brOnNull _ _ ts hh hl =>
        refine ⟨ops ts, refOp true hh, refOp false hh, rfl, rfl, fun hv => ?_⟩
        cases hh with
        | none => exact hv.elim
        | some hh => exact hv.nonNull hr
  case brOnNull =>
    refine same_pure hok hf (ASeqT.drop_top_to (v := .ref .null) ht fun hi => ?_)
    cases hi with | plain hi =>
      cases hi with | @brOnNull _ _ ts hh hl =>
        exact ⟨ops ts, _, rfl, fun _ => .single (.plain (.br (t₁ := []) hl))⟩
  case brOnNonNullNull =>
    refine same_pure hok hf (ASeqT.drop_top_to (v := .ref .null) ht fun hi => ?_)
    cases hi with | plain hi =>
      cases hi with | @brOnNonNull _ _ ts n hh hl =>
        exact ⟨ops ts, _, rfl, fun _ => .nil⟩
  case callRef =>
    refine same_pure hok hf (ASeqT.drop_top_to (v := .ref (.func _)) ht fun hi => ?_)
    cases hi with | plain hi =>
      cases hi with | @callRef _ _ dt ft hy he =>
        refine ⟨ops ft.params, _, rfl, fun hv => ?_⟩
        obtain ⟨fi, hfi, -, hh⟩ := hv
        have hdt : fi.type = dt := by
          rcases hh with hh | ⟨d, hd, hf'⟩
          · simpa using hh
          · simp at hf'
        exact .single (.invoke hfi (hdt ▸ he))
  case returnCallRef =>
    refine same_pure hok hf (ASeqT.drop_top_to (v := .ref (.func _)) ht fun hi => ?_)
    cases hi with | plain hi =>
      cases hi with | @returnCallRef _ _ dt ft rs t₃ t₄ hy he hr hs =>
        refine ⟨t₃ ++ ops ft.params, _, rfl, fun hv => ?_⟩
        obtain ⟨fi, hfi, -, hh⟩ := hv
        have hdt : fi.type = dt := by
          rcases hh with hh | ⟨d, hd, hf'⟩
          · simpa using hh
          · simp at hf'
        exact .single (.returnInvoke hfi (hdt ▸ he) hr hs)
  case returnCallIndirect htarget =>
    refine same_pure hok hf (ht.drop_selector fun hi => ?_)
    cases hi with | plain hi =>
      cases hi with | @returnCallIndirect _ _ _ tt ft rs t₃ t₄ htt he hy hr hs =>
        obtain ⟨ta, ti, fi, dt, _, _, _, hfi, hdt, hfd⟩ := htarget
        have hb := hy
        rw [Context.typeAt, hf.types, hdt, Option.bind_some] at hb
        exact ⟨t₃ ++ ops ft.params, by simp [List.append_assoc],
          .single (.returnInvoke hfi (by rw [hfd]; exact hb) hr hs)⟩
  case brOnNonNull hr =>
    refine same_pure hok hf (ASeqT.drop_top_to ht fun hi => ?_)
    cases hi with | plain hi =>
      cases hi with | @brOnNonNull _ _ ts n hh hl =>
        refine ⟨ops ts, _, rfl, fun hv => ?_⟩
        have h1 := (AInstrT.value (s := _) (C := C) (hv.nonNull hr)).frame (ops ts)
        simp only [List.append_nil] at h1
        have hm : Matches (ops ts ++ [.val (.ref ⟨false, hh⟩)]) (ops (ts ++ [.ref ⟨n, hh⟩])) := by
          simpa [ops] using (Matches.refl (ops ts)).append
            (.cons (show OpType.Matches (.val (.ref ⟨false, hh⟩)) (.val (.ref ⟨n, hh⟩)) from
              ⟨(fun h => nomatch h), .inl rfl⟩) .nil)
        have h2 := ASeqT.snoc (t₀ := []) h1 hm (by
          rw [ASeqT.after_pure C (by simp [↓Val.instr_sets']) (by simp [↓Val.instr_dead'])]
          exact .plain (.br (t₁ := []) (t₂ := ops ts) hl))
        simpa using h2
  case throwRefInstrs =>
    exact same hok hf (ASeqT.throwing_typed ht.throwing_addr _ _)
      (Context.Entails.to_dead_after _ _ (by simp [AInstr.dead]))
  case throwRefLabel =>
    obtain ⟨p, x, y, z, -, -, -, hi⟩ := ASeqT.single_iff.mp ht
    cases hi with | label hn hc hb =>
      exact same hok hf (ASeqT.throwing_typed
        (ASeqT.throwing_addr (pre := []) (post := []) (by simpa using hb)) _ _)
        (Context.Entails.to_dead_after _ _ (by simp [AInstr.dead]))
  case throwRefFrame =>
    obtain ⟨p, x, y, z, -, -, -, hi⟩ := ASeqT.single_iff.mp ht
    cases hi with | frame hn hf₀ hb =>
      exact same hok hf (ASeqT.throwing_typed
        (ASeqT.throwing_addr (pre := []) (post := []) (by simpa using hb)) _ _)
        (Context.Entails.to_dead_after _ _ (by simp [AInstr.dead]))
  case returnInvoke L hfn hft hlen =>
    exact same_pure hok hf (ht.returnInvoke L hfn hft hlen)

theorem preservation : Preservation := by
  intro H c c' ts hH hok hs
  obtain ⟨hstore, C, hf, ht⟩ := hok
  obtain ⟨he, hs', D, hc, hf', ht', -⟩ := fragment_preservation hH hs C [] (ops ts)
    hstore hf.ctx ht
  have hl : D.labels = [] := hc.labels.symm.trans hf.noLabels
  have hr : D.return_ = none := hc.return_.symm.trans hf.noReturn
  have hclear : ({ D with labels := [], return_ := none } : Context) = D := by rw [← hl, ← hr]
  exact ⟨he, hs', D, hclear ▸ hf'.frameT, ht'⟩

end FVA.Wasm.Valid
