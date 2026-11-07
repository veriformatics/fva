import FVA.Proof.Exec.HostFocus

/-!
# Growth policy (U27 T1)

`StepP H fits` against the spec's `Step H` (`fits = false`): monotone in the host relation, the
`true` policy included in `false`, and total wherever `false` steps (a growth failure that the
embedder refuses has its success in its place).
-/

namespace FVA.Wasm.Exec

open FVA.Wasm

/-- A step under host relation `H` and policy `fits` is one under any larger host relation and
any policy that grants growth no more often. -/
theorem StepP.map {H H' : HostSem} {fits fits' : Bool}
    (hH : ∀ id s vs o, H id s vs o → H' id s vs o) (hf : fits' = true → fits = true)
    {c d : Config} (h : StepP H fits c d) : StepP H' fits' c d := by
  induction h
  case num => exact .num ‹_›
  case refIsNull => exact .refIsNull
  case refFunc => exact .refFunc ‹_›
  case drop => exact .drop
  case select => exact .select
  case localGet => exact .localGet ‹_›
  case localSet => exact .localSet ‹_›
  case localTee => exact .localTee
  case globalGet => exact .globalGet ‹_› ‹_›
  case globalSet => exact .globalSet ‹_› ‹_›
  case tableGet => exact .tableGet ‹_› ‹_› ‹_›
  case tableGetTrap => exact .tableGetTrap ‹_› ‹_› ‹_›
  case tableSet => exact .tableSet ‹_› ‹_› ‹_›
  case tableSetTrap => exact .tableSetTrap ‹_› ‹_› ‹_›
  case tableSize => exact .tableSize ‹_› ‹_›
  case tableGrow => exact .tableGrow ‹_› ‹_› ‹_›
  case tableGrowFail =>
    rename_i hp
    exact .tableGrowFail fun e => hp (hf e)
  case tableFillTrap => exact .tableFillTrap ‹_› ‹_› ‹_›
  case tableFillZero => exact .tableFillZero ‹_› ‹_› ‹_›
  case tableFill => exact .tableFill ‹_› ‹_› ‹_› ‹_›
  case tableCopyTrap => exact .tableCopyTrap ‹_› ‹_› ‹_›
  case tableCopyZero => exact .tableCopyZero ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case tableCopyUp => exact .tableCopyUp ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case tableCopyDown => exact .tableCopyDown ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case tableInitTrap => exact .tableInitTrap ‹_› ‹_› ‹_›
  case tableInitZero => exact .tableInitZero ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case tableInit => exact .tableInit ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case elemDrop => exact .elemDrop ‹_› ‹_›
  case load => exact .load ‹_› ‹_› ‹_›
  case loadTrap => exact .loadTrap ‹_› ‹_› ‹_›
  case loadPacked => exact .loadPacked ‹_› ‹_› ‹_›
  case loadPackedTrap => exact .loadPackedTrap ‹_› ‹_› ‹_›
  case store => exact .store ‹_› ‹_› ‹_› ‹_›
  case storeTrap => exact .storeTrap ‹_› ‹_› ‹_› ‹_›
  case storePacked => exact .storePacked ‹_› ‹_› ‹_› ‹_›
  case storePackedTrap => exact .storePackedTrap ‹_› ‹_› ‹_› ‹_›
  case memorySize => exact .memorySize ‹_› ‹_›
  case memoryGrow => exact .memoryGrow ‹_› ‹_› ‹_›
  case memoryGrowFail =>
    rename_i hp
    exact .memoryGrowFail fun e => hp (hf e)
  case memoryFillTrap => exact .memoryFillTrap ‹_› ‹_› ‹_›
  case memoryFillZero => exact .memoryFillZero ‹_› ‹_› ‹_›
  case memoryFill => exact .memoryFill ‹_› ‹_› ‹_› ‹_›
  case memoryCopyTrap => exact .memoryCopyTrap ‹_› ‹_› ‹_›
  case memoryCopyZero => exact .memoryCopyZero ‹_› ‹_› ‹_› ‹_›
  case memoryCopyUp => exact .memoryCopyUp ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case memoryCopyDown => exact .memoryCopyDown ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case memoryInitTrap => exact .memoryInitTrap ‹_› ‹_› ‹_› ‹_›
  case memoryInitZero => exact .memoryInitZero ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case memoryInit => exact .memoryInit ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case dataDrop => exact .dataDrop ‹_› ‹_›
  case nop => exact .nop
  case unreachable => exact .unreachable
  case block => exact .block ‹_› ‹_›
  case loop => exact .loop ‹_› ‹_›
  case ifTrue => exact .ifTrue ‹_›
  case ifFalse => exact .ifFalse
  case labelExit => exact .labelExit
  case br => exact .br _ ‹_›
  case brIfTrue => exact .brIfTrue ‹_›
  case brIfFalse => exact .brIfFalse
  case brTable => exact .brTable
  case return_ => exact .return_ _ ‹_›
  case call => exact .call ‹_›
  case callIndirect => exact .callIndirect ‹_›
  case callIndirectTrap => exact .callIndirectTrap ‹_›
  case invoke => exact .invoke ‹_› ‹_›
  case frameExit => exact .frameExit ‹_›
  case invokeHost =>
    rename_i h₁ h₂ h₃
    exact .invokeHost h₁ h₂ (hH _ _ _ _ h₃)
  case invokeHostTrap =>
    rename_i h₁ h₂ h₃
    exact .invokeHostTrap h₁ h₂ (hH _ _ _ _ h₃)
  case invokeHostDiverge =>
    rename_i h₁ h₂ h₃
    exact .invokeHostDiverge h₁ h₂ (hH _ _ _ _ h₃)
  case seq ih => exact .seq ih
  case label ih => exact .label ih
  case frame ih => exact .frame ih
  case trap => exact .trap _ ‹_›
  case trapFrame => exact .trapFrame

theorem StepP.mono {H H' : HostSem} {fits : Bool}
    (hH : ∀ id s vs o, H id s vs o → H' id s vs o) {c d : Config} (h : StepP H fits c d) :
    StepP H' fits c d :=
  h.map hH id

theorem StepP.fits_le {H : HostSem} {c d : Config} (h : StepP H true c d) : Step H c d :=
  h.map (fun _ _ _ _ => id) (fun _ => rfl)

/-- Every policy's step is a step of the spec. -/
theorem StepP.toStep {H : HostSem} {fits : Bool} {c d : Config} (h : StepP H fits c d) :
    Step H c d :=
  h.map (fits' := false) (fun _ _ _ _ => id) nofun

theorem StepP.fits_total {H : HostSem} {c d : Config} (h : Step H c d) :
    ∃ d', StepP H true c d' := by
  induction h
  case num => exact ⟨_, .num ‹_›⟩
  case refIsNull => exact ⟨_, .refIsNull⟩
  case refFunc => exact ⟨_, .refFunc ‹_›⟩
  case drop => exact ⟨_, .drop⟩
  case select => exact ⟨_, .select⟩
  case localGet => exact ⟨_, .localGet ‹_›⟩
  case localSet => exact ⟨_, .localSet ‹_›⟩
  case localTee => exact ⟨_, .localTee⟩
  case globalGet => exact ⟨_, .globalGet ‹_› ‹_›⟩
  case globalSet => exact ⟨_, .globalSet ‹_› ‹_›⟩
  case tableGet => exact ⟨_, .tableGet ‹_› ‹_› ‹_›⟩
  case tableGetTrap => exact ⟨_, .tableGetTrap ‹_› ‹_› ‹_›⟩
  case tableSet => exact ⟨_, .tableSet ‹_› ‹_› ‹_›⟩
  case tableSetTrap => exact ⟨_, .tableSetTrap ‹_› ‹_› ‹_›⟩
  case tableSize => exact ⟨_, .tableSize ‹_› ‹_›⟩
  case tableGrow => exact ⟨_, .tableGrow ‹_› ‹_› ‹_›⟩
  case tableGrowFail s f x r n _ =>
    by_cases hno : ∀ ta t, f.inst.tables[x]? = some ta → s.tables[ta]? = some t →
        t.grow n.toNat r = none
    · exact ⟨_, .tableGrowFail fun _ => hno⟩
    · push Not at hno
      obtain ⟨ta, t, ha, ht, hg⟩ := hno
      cases hg' : t.grow n.toNat r with
      | none => exact absurd hg' hg
      | some t' => exact ⟨_, .tableGrow ha ht hg'⟩
  case tableFillTrap => exact ⟨_, .tableFillTrap ‹_› ‹_› ‹_›⟩
  case tableFillZero => exact ⟨_, .tableFillZero ‹_› ‹_› ‹_›⟩
  case tableFill => exact ⟨_, .tableFill ‹_› ‹_› ‹_› ‹_›⟩
  case tableCopyTrap => exact ⟨_, .tableCopyTrap ‹_› ‹_› ‹_›⟩
  case tableCopyZero => exact ⟨_, .tableCopyZero ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›⟩
  case tableCopyUp => exact ⟨_, .tableCopyUp ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›⟩
  case tableCopyDown => exact ⟨_, .tableCopyDown ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›⟩
  case tableInitTrap => exact ⟨_, .tableInitTrap ‹_› ‹_› ‹_›⟩
  case tableInitZero => exact ⟨_, .tableInitZero ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›⟩
  case tableInit => exact ⟨_, .tableInit ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›⟩
  case elemDrop => exact ⟨_, .elemDrop ‹_› ‹_›⟩
  case load => exact ⟨_, .load ‹_› ‹_› ‹_›⟩
  case loadTrap => exact ⟨_, .loadTrap ‹_› ‹_› ‹_›⟩
  case loadPacked => exact ⟨_, .loadPacked ‹_› ‹_› ‹_›⟩
  case loadPackedTrap => exact ⟨_, .loadPackedTrap ‹_› ‹_› ‹_›⟩
  case store => exact ⟨_, .store ‹_› ‹_› ‹_› ‹_›⟩
  case storeTrap => exact ⟨_, .storeTrap ‹_› ‹_› ‹_› ‹_›⟩
  case storePacked => exact ⟨_, .storePacked ‹_› ‹_› ‹_› ‹_›⟩
  case storePackedTrap => exact ⟨_, .storePackedTrap ‹_› ‹_› ‹_› ‹_›⟩
  case memorySize => exact ⟨_, .memorySize ‹_› ‹_›⟩
  case memoryGrow => exact ⟨_, .memoryGrow ‹_› ‹_› ‹_›⟩
  case memoryGrowFail s f n _ =>
    by_cases hno : ∀ a mem, f.inst.mems[0]? = some a → s.mems[a]? = some mem →
        mem.grow n.toNat = none
    · exact ⟨_, .memoryGrowFail fun _ => hno⟩
    · push Not at hno
      obtain ⟨a, mem, ha, hm, hg⟩ := hno
      cases hg' : mem.grow n.toNat with
      | none => exact absurd hg' hg
      | some mem' => exact ⟨_, .memoryGrow ha hm hg'⟩
  case memoryFillTrap => exact ⟨_, .memoryFillTrap ‹_› ‹_› ‹_›⟩
  case memoryFillZero => exact ⟨_, .memoryFillZero ‹_› ‹_› ‹_›⟩
  case memoryFill => exact ⟨_, .memoryFill ‹_› ‹_› ‹_› ‹_›⟩
  case memoryCopyTrap => exact ⟨_, .memoryCopyTrap ‹_› ‹_› ‹_›⟩
  case memoryCopyZero => exact ⟨_, .memoryCopyZero ‹_› ‹_› ‹_› ‹_›⟩
  case memoryCopyUp => exact ⟨_, .memoryCopyUp ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›⟩
  case memoryCopyDown => exact ⟨_, .memoryCopyDown ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›⟩
  case memoryInitTrap => exact ⟨_, .memoryInitTrap ‹_› ‹_› ‹_› ‹_›⟩
  case memoryInitZero => exact ⟨_, .memoryInitZero ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›⟩
  case memoryInit => exact ⟨_, .memoryInit ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›⟩
  case dataDrop => exact ⟨_, .dataDrop ‹_› ‹_›⟩
  case nop => exact ⟨_, .nop⟩
  case unreachable => exact ⟨_, .unreachable⟩
  case block => exact ⟨_, .block ‹_› ‹_›⟩
  case loop => exact ⟨_, .loop ‹_› ‹_›⟩
  case ifTrue => exact ⟨_, .ifTrue ‹_›⟩
  case ifFalse => exact ⟨_, .ifFalse⟩
  case labelExit => exact ⟨_, .labelExit⟩
  case br => exact ⟨_, .br _ ‹_›⟩
  case brIfTrue => exact ⟨_, .brIfTrue ‹_›⟩
  case brIfFalse => exact ⟨_, .brIfFalse⟩
  case brTable => exact ⟨_, .brTable⟩
  case return_ => exact ⟨_, .return_ _ ‹_›⟩
  case call => exact ⟨_, .call ‹_›⟩
  case callIndirect => exact ⟨_, .callIndirect ‹_›⟩
  case callIndirectTrap => exact ⟨_, .callIndirectTrap ‹_›⟩
  case invoke => exact ⟨_, .invoke ‹_› ‹_›⟩
  case frameExit => exact ⟨_, .frameExit ‹_›⟩
  case invokeHost =>
    rename_i h₁ h₂ h₃
    exact ⟨_, .invokeHost h₁ h₂ h₃⟩
  case invokeHostTrap =>
    rename_i h₁ h₂ h₃
    exact ⟨_, .invokeHostTrap h₁ h₂ h₃⟩
  case invokeHostDiverge =>
    rename_i h₁ h₂ h₃
    exact ⟨_, .invokeHostDiverge h₁ h₂ h₃⟩
  case seq ih =>
    obtain ⟨⟨s', f', es'⟩, h'⟩ := ih
    exact ⟨_, .seq h'⟩
  case label ih =>
    obtain ⟨⟨s', f', es'⟩, h'⟩ := ih
    exact ⟨_, .label h'⟩
  case frame ih =>
    obtain ⟨⟨s', f', es'⟩, h'⟩ := ih
    exact ⟨_, .frame h'⟩
  case trap => exact ⟨_, .trap _ ‹_›⟩
  case trapFrame => exact ⟨_, .trapFrame⟩

end FVA.Wasm.Exec
