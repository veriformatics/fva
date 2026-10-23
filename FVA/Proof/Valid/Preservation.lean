import FVA.Proof.Valid.Call
import FVA.Proof.Valid.Memory
import FVA.Proof.Valid.Variables

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

/-- Fragment postcondition; context transport accounts for grown table/memory minima. -/
def Preserved (s : Store) (C : Context) (a b : List OpType) (c : Config) : Prop :=
  s.Extends c.store ∧ StoreOK c.store ∧ ∃ D, C.Entails D ∧ FrameCtx c.store c.frame D ∧
    ASeqT c.store D c.instrs ⟨a, b⟩

private theorem same {s : Store} {f : Frame} {C : Context} {es : List AInstr}
    {a b : List OpType} (hok : StoreOK s) (hf : FrameCtx s f C)
    (he : ASeqT s C es ⟨a, b⟩) : Preserved s C a b ⟨s, f, es⟩ :=
  ⟨Store.Extends.refl s, hok, C, Context.Entails.refl C, hf, he⟩

private theorem changed {s s' : Store} {f : Frame} {C : Context} {es : List AInstr}
    {a b : List OpType} (hs : s.Extends s' ∧ StoreOK s') (hf : FrameCtx s f C)
    (he : ASeqT s C es ⟨a, b⟩) : Preserved s C a b ⟨s', f, es⟩ := by
  obtain ⟨D, hf', hc⟩ := hf.extendStore hs.1
  exact ⟨hs.1, hs.2, D, hc, hf', he.transport hs.1 hc⟩

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
        Preserved c.store C a b c' := by
  induction step <;> intro C a b hok hf ht
  case num hr => exact same hok hf (ht.numeric hr)
  case refIsNull => exact same hok hf ht.refIsNull
  case refFunc ha => exact same hok hf (ht.refFunc hf ha)
  case drop => exact same hok hf ht.drop
  case select => exact same hok hf ht.select
  case localGet hv => exact same hok hf (ht.localGet hf hv)
  case localSet hx =>
    obtain ⟨hf', ht'⟩ := ht.localSet hf
    exact same hok hf' ht'
  case localTee => exact same hok hf ht.localTee
  case globalGet ha hg => exact same hok hf (ht.globalGet hok hf ha hg)
  case globalSet ha hg =>
    obtain ⟨hmut, hv, hm⟩ := ht.globalSet hf ha hg
    exact changed (hok.setGlobal hg hmut hv) hf (ASeqT.nil_iff.mpr hm)
  case tableGet ha hti hr => exact same hok hf (ht.tableGet hok hf ha hti hr)
  case tableGetTrap => exact same hok hf (.single .trap)
  case tableSet ha hti hi =>
    obtain ⟨hv, hm⟩ := ht.tableSet hf ha hti
    exact changed (hok.writeTable hti _ hv) hf (ASeqT.nil_iff.mpr hm)
  case tableSetTrap => exact same hok hf (.single .trap)
  case tableSize => exact same hok hf (ht.tableSize _)
  case tableGrow ha hti hg =>
    have hv := ht.tableGrow_ref hf ha hti
    exact changed (hok.growTable hti hg hv) hf (ht.tableGrow _)
  case tableGrowFail => exact same hok hf (ht.tableGrow _)
  case tableFillTrap => exact same hok hf (.single .trap)
  case tableFillZero => exact same hok hf ht.tableFillZero
  case tableFill => exact same hok hf ht.tableFill
  case tableCopyTrap => exact same hok hf (.single .trap)
  case tableCopyZero => exact same hok hf ht.tableCopyZero
  case tableCopyUp => exact same hok hf ht.tableCopyUp
  case tableCopyDown => exact same hok hf ht.tableCopyDown
  case tableInitTrap => exact same hok hf (.single .trap)
  case tableInitZero => exact same hok hf ht.tableInitZero
  case tableInit ha hel hti hei hn hsrc hdst hr =>
    exact same hok hf (ht.tableInit hok hf hel hei hr)
  case elemDrop ha hei => exact changed (hok.dropElem hei) hf (ASeqT.nil_iff.mpr ht.elemDrop)
  case load => exact same hok hf (ht.load _)
  case loadTrap => exact same hok hf (.single .trap)
  case loadPacked => exact same hok hf (ht.loadPacked _)
  case loadPackedTrap => exact same hok hf (.single .trap)
  case store ha hmem hv hbound =>
    exact changed (hok.writeMem hmem _ _ _) hf (ASeqT.nil_iff.mpr ht.store)
  case storeTrap => exact same hok hf (.single .trap)
  case storePacked ha hmem hv hbound =>
    exact changed (hok.writeMem hmem _ _ _) hf (ASeqT.nil_iff.mpr ht.storePacked)
  case storePackedTrap => exact same hok hf (.single .trap)
  case memorySize => exact same hok hf (ht.memorySize _)
  case memoryGrow ha hmem hg => exact changed (hok.growMem hmem hg) hf (ht.memoryGrow _)
  case memoryGrowFail => exact same hok hf (ht.memoryGrow _)
  case memoryFillTrap => exact same hok hf (.single .trap)
  case memoryFillZero => exact same hok hf ht.memoryFillZero
  case memoryFill => exact same hok hf ht.memoryFill
  case memoryCopyTrap => exact same hok hf (.single .trap)
  case memoryCopyZero => exact same hok hf ht.memoryCopyZero
  case memoryCopyUp => exact same hok hf ht.memoryCopyUp
  case memoryCopyDown => exact same hok hf ht.memoryCopyDown
  case memoryInitTrap => exact same hok hf (.single .trap)
  case memoryInitZero => exact same hok hf ht.memoryInitZero
  case memoryInit => exact same hok hf (ht.memoryInit _)
  case dataDrop ha hdi => exact changed (hok.dropData hdi) hf (ASeqT.nil_iff.mpr ht.dataDrop)
  case nop => exact same hok hf ht.nop
  case unreachable => exact same hok hf (.single .trap)
  case block hbt hlen => exact same hok hf (ht.block hf hbt hlen)
  case loop hbt hlen => exact same hok hf (ht.loop hf hbt hlen)
  case ifTrue => exact same hok hf ht.ifTrue
  case ifFalse => exact same hok hf ht.ifFalse
  case labelExit => exact same hok hf ht.labelExit
  case br L hlen => exact same hok hf (ht.br L hlen)
  case brIfTrue => exact same hok hf ht.brIfTrue
  case brIfFalse => exact same hok hf ht.brIfFalse
  case brTable => exact same hok hf ht.brTable
  case return_ L hlen => exact same hok hf (ht.return_ L hlen)
  case call ha => exact same hok hf (ht.call hf ha)
  case callIndirect htarget => exact same hok hf (ht.callIndirect hf htarget)
  case callIndirectTrap => exact same hok hf (.single .trap)
  case invoke hfi hlen => exact same hok hf (ht.invoke hok hfi hlen)
  case frameExit => exact same hok hf ht.frameExit
  case invokeHost hfi hlen hh =>
    obtain ⟨p, hp, hout, hargs⟩ := ht.invoke_inv hfi hlen
    obtain ⟨he, hres⟩ := (hH.1 _ _ _ _ _ hfi hargs).2 _ hh
    have hok' := hH.2 _ _ _ _ _ _ hok hfi hargs hh
    obtain ⟨D, hf', hc⟩ := hf.extendStore he
    exact ⟨he, hok', D, hc, hf', .sub ((ASeqT.values hres p).input hp) hout⟩
  case invokeHostTrap hfi hlen hh =>
    obtain ⟨p, hp, hout, hargs⟩ := ht.invoke_inv hfi hlen
    have he := (hH.1 _ _ _ _ _ hfi hargs).2 _ hh
    have hok' := hH.2 _ _ _ _ _ _ hok hfi hargs hh
    exact changed ⟨he, hok'⟩ hf (.single .trap)
  case invokeHostDiverge => exact same hok hf ht
  case seq step ih =>
    obtain ⟨q, hpre, hrest⟩ := ht.split
    obtain ⟨p, hvals, hin⟩ := hpre.split
    obtain ⟨he, hok', D, hc, hf', hout⟩ := ih _ _ _ hok hf hin
    exact ⟨he, hok', D, hc, hf',
      ((hvals.transport he hc).append hout).append (hrest.transport he hc)⟩
  case label step ih =>
    obtain ⟨p, x, y, z, hin, hout, hm, hi⟩ := ASeqT.single_iff.mp ht
    cases hi with | @label _ _ _ _ t₁ t₂ hn hc hb =>
      obtain ⟨he, hok', D', hc', hf', hb'⟩ := ih _ _ _ hok (hf.withLabel t₁) hb
      let D : Context := { D' with labels := C.labels }
      have hCD : C.Entails D := { hc' with labels := rfl }
      have hDD : D.withLabel t₁ = D' := by
        change { D' with labels := t₁ :: C.labels } = D'
        have hl : t₁ :: C.labels = D'.labels := hc'.labels
        rw [hl]
      refine ⟨he, hok', D, hCD, hf'.withLabels C.labels, ASeqT.single_iff.mpr ?_⟩
      exact ⟨p, x, _, _, hin, hout, hm,
        .label hn (hc.transport hCD) (hDD.symm ▸ hb')⟩
  case frame step ih =>
    obtain ⟨p, x, y, z, hin, hout, hm, hi⟩ := ASeqT.single_iff.mp ht
    cases hi with | @frame _ Cinner _ _ _ ts hn hinner hb =>
      obtain ⟨he, hok', D', hc', hf', hb'⟩ :=
        ih _ _ _ hok (hinner.ctx.withReturn (some ts)) hb
      have hl : D'.labels = [] := hc'.labels.symm.trans hinner.noLabels
      have hr : D'.return_ = some ts := hc'.return_.symm
      have hDD : ({ { D' with labels := [], return_ := none } with
          return_ := some ts } : Context) = D' := by
        change { D' with labels := [], return_ := some ts } = D'
        rw [← hl, ← hr]
      obtain ⟨D, houter, hCD⟩ := hf.extendStore he
      refine ⟨he, hok', D, hCD, houter, ASeqT.single_iff.mpr ?_⟩
      exact ⟨p, x, _, _, hin, hout, hm, .frame hn hf'.frameT (hDD.symm ▸ hb')⟩
  case trap => exact same hok hf (.single .trap)
  case trapFrame => exact same hok hf (.single .trap)

theorem preservation : Preservation := by
  intro H c c' ts hH hok hs
  obtain ⟨hstore, C, hf, ht⟩ := hok
  obtain ⟨he, hs', D, hc, hf', ht'⟩ := fragment_preservation hH hs C [] (ops ts)
    hstore hf.ctx ht
  have hl : D.labels = [] := hc.labels.symm.trans hf.noLabels
  have hr : D.return_ = none := hc.return_.symm.trans hf.noReturn
  have hclear : ({ D with labels := [], return_ := none } : Context) = D := by rw [← hl, ← hr]
  exact ⟨he, hs', D, hclear ▸ hf'.frameT, ht'⟩

end FVA.Wasm.Valid
