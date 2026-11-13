import FVA.Proof.Exec.Policy
import FVA.Spec.Exec.System

/-!
# Process executions (U27 T2–T4)

Every step is host-free or the focused host call's outcome (`free_or_host`); the system relation
under an environment is included in the general one and keeps a step wherever it has one; the
transfer rules a `SysMust` proof is built from: a unique core step, a pending trap, a pending
throw (uncaught, or reaching its handler), a finished state, a host call over every allowed
outcome; an allowed divergence refutes `SysMust`.
-/

namespace FVA.Wasm.Exec

open FVA.Wasm Ref

set_option maxHeartbeats 1000000 in
/-- A step is host-free, or the focused host call's allowed outcome, in place. -/
theorem free_or_host {H : HostSem} {fits : Bool} {c d : Config} (h : StepP H fits c d) :
    StepP NoHost fits c d ∨
    ∀ (stk : List Val) (rest : List AInstr), ∃ a args k dt id o,
      seq c.store c.frame stk (c.instrs ++ rest) = .host a args k ∧
      c.store.funcs[a]? = some (.host dt id) ∧ H id c.store args o ∧
      d.store = hostStore c.store o ∧ d.frame = c.frame ∧
      vals stk.reverse ++ d.instrs ++ rest = k.result a args o := by
  induction h
  case invokeHost s s' f a dt ft id vs res hf hft hlen hH =>
    refine .inr fun stk rest =>
      ⟨a, vs, .seq stk.reverse .hole rest, dt, id, .returned s' res, ?_, hf, hH, rfl, rfl, ?_⟩
    · rw [List.append_assoc, seq_vals]
      simp [seq, toVal, atInstr, hf, hft, ← hlen, Bool.cond_eq_ite, Nat.blt_eq]
    · simp [HCtx.result, HCtx.fill]
  case invokeHostTrap s s' f a dt ft id vs hf hft hlen hH =>
    refine .inr fun stk rest =>
      ⟨a, vs, .seq stk.reverse .hole rest, dt, id, .trapped s', ?_, hf, hH, rfl, rfl, ?_⟩
    · rw [List.append_assoc, seq_vals]
      simp [seq, toVal, atInstr, hf, hft, ← hlen, Bool.cond_eq_ite, Nat.blt_eq]
    · simp [HCtx.result, HCtx.fill]
  case invokeHostDiverge s f a dt ft id vs hf hft hlen hH =>
    refine .inr fun stk rest =>
      ⟨a, vs, .seq stk.reverse .hole rest, dt, id, .diverged, ?_, hf, hH, rfl, rfl, ?_⟩
    · rw [List.append_assoc, seq_vals]
      simp [seq, toVal, atInstr, hf, hft, ← hlen, Bool.cond_eq_ite, Nat.blt_eq]
    · simp [HCtx.result, HCtx.fill]
  case seq s f s' f' es es' vs tail h ih =>
    rcases ih with ih | ih
    · exact .inl (.seq ih)
    · refine .inr fun stk rest => ?_
      obtain ⟨a, args, k, ft, id, o, hq, hf, hH, hs, hfr, hk⟩ :=
        ih (vs.reverse ++ stk) (tail ++ rest)
      refine ⟨a, args, k, ft, id, o, ?_, hf, hH, hs, hfr, ?_⟩
      · simpa only [List.append_assoc, seq_vals] using hq
      · simpa [List.reverse_append, List.append_assoc] using hk
  case label s f s' f' n cont es es' h ih =>
    rcases ih with ih | ih
    · exact .inl (.label ih)
    · refine .inr fun stk rest => ?_
      obtain ⟨a, args, k, ft, id, o, hq, hf, hH, hs, hfr, hk⟩ := ih [] []
      simp only [List.append_nil] at hq
      refine ⟨a, args, .seq stk.reverse (.label n cont k) rest, ft, id, o, ?_, hf, hH, hs, hfr, ?_⟩
      · simp [seq, toVal, atInstr, hq]
      · simp only [List.append_nil, List.reverse_nil, vals, List.map_nil, List.nil_append] at hk
        simp [hk]
  case frame s f s' n fi fi' es es' h ih =>
    rcases ih with ih | ih
    · exact .inl (.frame ih)
    · refine .inr fun stk rest => ?_
      obtain ⟨a, args, k, ft, id, o, hq, hf, hH, hs, hfr, hk⟩ := ih [] []
      simp only [List.append_nil] at hq
      refine ⟨a, args, .seq stk.reverse (.frame n fi k) rest, ft, id, o, ?_, hf, hH, hs, rfl, ?_⟩
      · simp [seq, toVal, atInstr, hq]
      · simp only [List.append_nil, List.reverse_nil, vals, List.map_nil, List.nil_append] at hk
        simp only at hfr
        simp [hk, hfr]
  case num => exact .inl (.num ‹_›)
  case refNull => exact .inl .refNull
  case refIsNull => exact .inl (.refIsNull)
  case refFunc => exact .inl (.refFunc ‹_›)
  case drop => exact .inl (.drop)
  case select => exact .inl (.select)
  case localGet => exact .inl (.localGet ‹_›)
  case localSet => exact .inl (.localSet ‹_›)
  case localTee => exact .inl (.localTee)
  case globalGet => exact .inl (.globalGet ‹_› ‹_›)
  case globalSet => exact .inl (.globalSet ‹_› ‹_›)
  case tableGet => exact .inl (.tableGet ‹_› ‹_› ‹_›)
  case tableGetTrap => exact .inl (.tableGetTrap ‹_› ‹_› ‹_›)
  case tableSet => exact .inl (.tableSet ‹_› ‹_› ‹_›)
  case tableSetTrap => exact .inl (.tableSetTrap ‹_› ‹_› ‹_›)
  case tableSize => exact .inl (.tableSize ‹_› ‹_›)
  case tableGrow => exact .inl (.tableGrow ‹_› ‹_› ‹_›)
  case tableGrowFail => exact .inl (.tableGrowFail ‹_›)
  case tableFillTrap => exact .inl (.tableFillTrap ‹_› ‹_› ‹_›)
  case tableFillZero => exact .inl (.tableFillZero ‹_› ‹_› ‹_›)
  case tableFill => exact .inl (.tableFill ‹_› ‹_› ‹_› ‹_›)
  case tableCopyTrap => exact .inl (.tableCopyTrap ‹_› ‹_› ‹_›)
  case tableCopyZero => exact .inl (.tableCopyZero ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›)
  case tableCopyUp => exact .inl (.tableCopyUp ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›)
  case tableCopyDown => exact .inl (.tableCopyDown ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›)
  case tableInitTrap => exact .inl (.tableInitTrap ‹_› ‹_› ‹_›)
  case tableInitZero => exact .inl (.tableInitZero ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›)
  case tableInit => exact .inl (.tableInit ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›)
  case elemDrop => exact .inl (.elemDrop ‹_› ‹_›)
  case load => exact .inl (.load ‹_› ‹_› ‹_›)
  case loadTrap => exact .inl (.loadTrap ‹_› ‹_› ‹_›)
  case loadPacked => exact .inl (.loadPacked ‹_› ‹_› ‹_›)
  case loadPackedTrap => exact .inl (.loadPackedTrap ‹_› ‹_› ‹_›)
  case store => exact .inl (.store ‹_› ‹_› ‹_› ‹_›)
  case storeTrap => exact .inl (.storeTrap ‹_› ‹_› ‹_› ‹_›)
  case storePacked => exact .inl (.storePacked ‹_› ‹_› ‹_› ‹_›)
  case storePackedTrap => exact .inl (.storePackedTrap ‹_› ‹_› ‹_› ‹_›)
  case memorySize => exact .inl (.memorySize ‹_› ‹_›)
  case memoryGrow => exact .inl (.memoryGrow ‹_› ‹_› ‹_›)
  case memoryGrowFail => exact .inl (.memoryGrowFail ‹_›)
  case memoryFillTrap => exact .inl (.memoryFillTrap ‹_› ‹_› ‹_›)
  case memoryFillZero => exact .inl (.memoryFillZero ‹_› ‹_› ‹_›)
  case memoryFill => exact .inl (.memoryFill ‹_› ‹_› ‹_› ‹_›)
  case memoryCopyTrap => exact .inl (.memoryCopyTrap ‹_› ‹_› ‹_›)
  case memoryCopyZero => exact .inl (.memoryCopyZero ‹_› ‹_› ‹_› ‹_›)
  case memoryCopyUp => exact .inl (.memoryCopyUp ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›)
  case memoryCopyDown => exact .inl (.memoryCopyDown ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›)
  case memoryInitTrap => exact .inl (.memoryInitTrap ‹_› ‹_› ‹_› ‹_›)
  case memoryInitZero => exact .inl (.memoryInitZero ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›)
  case memoryInit => exact .inl (.memoryInit ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›)
  case dataDrop => exact .inl (.dataDrop ‹_› ‹_›)
  case nop => exact .inl (.nop)
  case unreachable => exact .inl (.unreachable)
  case block => exact .inl (.block ‹_› ‹_›)
  case loop => exact .inl (.loop ‹_› ‹_›)
  case ifTrue => exact .inl (.ifTrue ‹_›)
  case ifFalse => exact .inl (.ifFalse)
  case labelExit => exact .inl (.labelExit)
  case br => exact .inl (.br _ ‹_›)
  case brIfTrue => exact .inl (.brIfTrue ‹_›)
  case brIfFalse => exact .inl (.brIfFalse)
  case brTable => exact .inl (.brTable)
  case return_ => exact .inl (.return_ _ ‹_›)
  case call => exact .inl (.call ‹_›)
  case callIndirect => exact .inl (.callIndirect ‹_›)
  case callIndirectTrap => exact .inl (.callIndirectTrap ‹_›)
  case invoke => exact .inl (.invoke ‹_› ‹_› ‹_›)
  case frameExit => exact .inl (.frameExit ‹_›)
  case trap => exact .inl (.trap _ ‹_›)
  case trapFrame => exact .inl (.trapFrame)
  case handler s f s' f' n cs es es' h ih =>
    rcases ih with ih | ih
    · exact .inl (.handler ih)
    · refine .inr fun stk rest => ?_
      obtain ⟨a, args, k, ft, id, o, hq, hf, hH, hs, hfr, hk⟩ := ih [] []
      simp only [List.append_nil] at hq
      refine ⟨a, args, .seq stk.reverse (.handler n cs k) rest, ft, id, o, ?_, hf, hH, hs, hfr,
        ?_⟩
      · simp [seq, toVal, atInstr, hq]
      · simp only [List.append_nil, List.reverse_nil, vals, List.map_nil, List.nil_append] at hk
        simp [hk]
  case tryTable => exact .inl (.tryTable ‹_› ‹_›)
  case handlerExit => exact .inl .handlerExit
  case throw => exact .inl (.throw ‹_› ‹_› ‹_› ‹_› ‹_›)
  case throwRefNull => exact .inl .throwRefNull
  case throwRefInstrs => exact .inl (.throwRefInstrs ‹_›)
  case throwRefLabel => exact .inl .throwRefLabel
  case throwRefFrame => exact .inl .throwRefFrame
  case throwRefHandlerEmpty => exact .inl .throwRefHandlerEmpty
  case throwRefCatch => exact .inl (.throwRefCatch ‹_› ‹_›)
  case throwRefCatchRef => exact .inl (.throwRefCatchRef ‹_› ‹_›)
  case throwRefCatchAll => exact .inl .throwRefCatchAll
  case throwRefCatchAllRef => exact .inl .throwRefCatchAllRef
  case throwRefHandlerNext => exact .inl (.throwRefHandlerNext ‹_›)
  case returnCall => exact .inl (.returnCall ‹_›)
  case returnCallRef => exact .inl .returnCallRef
  case returnCallRefNull => exact .inl .returnCallRefNull
  case returnCallIndirect => exact .inl (.returnCallIndirect ‹_›)
  case returnCallIndirectTrap => exact .inl (.returnCallIndirectTrap ‹_›)
  case callRef => exact .inl .callRef
  case callRefNull => exact .inl .callRefNull
  case refAsNonNull => exact .inl (.refAsNonNull ‹_›)
  case refAsNonNullNull => exact .inl .refAsNonNullNull
  case brOnNull => exact .inl .brOnNull
  case brOnNullValue => exact .inl (.brOnNullValue ‹_›)
  case brOnNonNull => exact .inl (.brOnNonNull ‹_›)
  case brOnNonNullNull => exact .inl .brOnNonNullNull
  case returnInvoke => exact .inl (.returnInvoke _ ‹_› ‹_› ‹_›)

/-- A focused host call has no host-free step. -/
theorem host_no_free {fits : Bool} {c d : Config} {a : Nat} {args : List Val} {k : HCtx}
    (hq : seq c.store c.frame [] c.instrs = .host a args k) : ¬ StepP NoHost fits c d := by
  intro h
  obtain ⟨_, _, _, _, hH, _⟩ := host_complete h [] [] a args k (by simpa using hq)
  exact hH

theorem sysStep_iff {W : World} {fits : Bool} {σ τ : W.St} {c d : Config} :
    SysStep W fits (σ, c) (τ, d) ↔ W.exited σ = none ∧
      ((StepP NoHost fits c d ∧ τ = σ) ∨ (StepP (W.host σ τ) fits c d ∧ ¬ Step NoHost c d)) :=
  Iff.rfl

theorem sysFinal_returned {W : World} {σ : W.St} {c : Config} {vs : List Val}
    (hl : W.exited σ = none) (hv : c.instrs = vals vs) :
    SysFinal W (σ, c) (.returned σ c.store vs) := by
  unfold SysFinal Final
  exact ⟨rfl, hl, rfl, hv⟩

theorem sysFinal_exited {W : World} {σ : W.St} {c : Config} {k : Nat}
    (he : W.exited σ = some k) : SysFinal W (σ, c) (.exited σ c.store k) := by
  unfold SysFinal
  exact ⟨rfl, he, rfl⟩

theorem sysFinal_abnormal {W : World} {σ : W.St} {c : Config} (hl : W.exited σ = none)
    (ht : c.instrs = [.trap]) : SysFinal W (σ, c) (.abnormal σ c.store) :=
  ⟨rfl, hl, .inl ⟨rfl, ht⟩⟩

theorem sysFinal_thrown {W : World} {σ : W.St} {c : Config} {a : Nat} (hl : W.exited σ = none)
    (ht : c.instrs = throwing a) : SysFinal W (σ, c) (.abnormal σ c.store) :=
  ⟨rfl, hl, .inr ⟨a, rfl, ht⟩⟩

/-- The exclusion's two forms agree on every step some host explains: such a step is host-free
under the spec's policy iff it is under `fits` (the Decision's `¬ StepP NoHost fits` = the
spec's `¬ Step NoHost`). -/
theorem host_free_iff {H : HostSem} {fits : Bool} {c d : Config} (h : StepP H fits c d) :
    Step NoHost c d ↔ StepP NoHost fits c d := by
  refine ⟨fun hn => ?_, StepP.toStep⟩
  rcases free_or_host h with hf | hh
  · exact hf
  · obtain ⟨a, args, k, -, -, -, hq, -⟩ := hh [] []
    simp only [List.append_nil] at hq
    exact absurd hn (host_no_free hq)

theorem exited_no_step {W : World} {fits : Bool} {σ : W.St} {c : Config} {y : W.St × Config}
    {k : Nat} (he : W.exited σ = some k) : ¬ SysStep W fits (σ, c) y := by
  intro h
  rcases y with ⟨τ, d⟩
  simp only [SysStep, he, reduceCtorEq, false_and] at h

theorem sysFinal_no_step {W : World} {fits : Bool} {x y : W.St × Config} {o : SysOutcome W.St}
    (hf : SysFinal W x o) : ¬ SysStep W fits x y := by
  rcases x with ⟨σ, c⟩
  rcases y with ⟨τ, d⟩
  intro hs
  simp only [SysStep] at hs
  obtain ⟨hl, hs⟩ := hs
  cases o with
  | exited σ' s k =>
    obtain ⟨_, he, _⟩ := hf
    rw [he] at hl
    cases hl
  | returned σ' s vs =>
    obtain ⟨_, _, hc⟩ := hf
    rcases hs with ⟨hs, _⟩ | ⟨hs, _⟩
    · exact no_step_final hc hs.toStep
    · exact no_step_final hc hs.toStep
  | abnormal σ' s =>
    obtain ⟨_, _, hc | ⟨_, hc⟩⟩ := hf <;> rcases hs with ⟨hs, _⟩ | ⟨hs, _⟩
    all_goals exact no_step_final hc hs.toStep

theorem sysFinal_unique {W : World} {x : W.St × Config} {o o' : SysOutcome W.St}
    (h : SysFinal W x o) (h' : SysFinal W x o') : o = o' := by
  rcases x with ⟨σ, c⟩
  have hab : ∀ {s : Store}, (Final c (.trapped s) ∨ ∃ a, Final c (.thrown s a)) → c.store = s := by
    rintro s (⟨h, -⟩ | ⟨_, h, -⟩) <;> exact h
  cases o <;> cases o' <;> simp only [SysFinal] at h h'
  all_goals obtain ⟨rfl, h1, h2⟩ := h
  all_goals obtain ⟨rfl, h1', h2'⟩ := h'
  all_goals first
    | (have hu := final_unique h2 h2'; simp_all)
    | (rcases h2' with h2' | ⟨_, h2'⟩ <;> have hu := final_unique h2 h2' <;> simp_all)
    | (rcases h2 with h2 | ⟨_, h2⟩ <;> have hu := final_unique h2 h2' <;> simp_all)
    | (have := hab h2; have := hab h2'; simp_all)
    | simp_all

/-- Every finished outcome reached from a `SysMust` state satisfies its postcondition. -/
theorem SysMust.outcome {W : World} {fits : Bool} {Q : SysOutcome W.St → Prop}
    {x y : W.St × Config} {o : SysOutcome W.St} (h : SysMust W fits Q x)
    (hs : Relation.ReflTransGen (SysStep W fits) x y) (hf : SysFinal W y o) : Q o := by
  induction h generalizing y with
  | done hx hq =>
    rcases hs.cases_head with rfl | ⟨z, hxz, _⟩
    · obtain rfl := sysFinal_unique hx hf
      exact hq
    · exact absurd hxz (sysFinal_no_step hx)
  | next hex _ ih =>
    rcases hs.cases_head with rfl | ⟨z, hxz, hzy⟩
    · obtain ⟨z, hz⟩ := hex
      exact absurd hz (sysFinal_no_step hf)
    · exact ih z hxz hzy hf

/-- The system relation under an environment is part of the general one (every growth may
fail, every host outcome of the world). -/
theorem sysStep_restrict_le {W : World} {E : W.St → W.St → HostSem} {x y : W.St × Config}
    (h : SysStep (W.restrict E) true x y) : SysStep W false x y := by
  rcases x with ⟨σ, c⟩
  rcases y with ⟨τ, d⟩
  obtain ⟨hl, hs⟩ := h
  refine ⟨hl, ?_⟩
  rcases hs with ⟨hs, hτ⟩ | ⟨hs, hn⟩
  · exact .inl ⟨hs.fits_le, hτ⟩
  · exact .inr ⟨hs.map (fun _ _ _ _ h => h.1) (fun _ => rfl), hn⟩

/-- An environment that keeps an outcome of every allowed call keeps a step wherever the
general relation has one. -/
theorem sysStep_restrict_total {W : World} {E : W.St → W.St → HostSem} (hE : Env.Total W E)
    {x : W.St × Config} (h : ∃ y, SysStep W false x y) :
    ∃ y, SysStep (W.restrict E) true x y := by
  rcases x with ⟨σ, c⟩
  obtain ⟨⟨τ, d⟩, hsys⟩ := h
  obtain ⟨hl, hs⟩ := sysStep_iff.mp hsys
  rcases hs with ⟨hs, -⟩ | ⟨hs, hn⟩
  · obtain ⟨d', hd'⟩ := hs.fits_total
    exact ⟨(σ, d'), sysStep_iff.mpr ⟨hl, .inl ⟨hd', rfl⟩⟩⟩
  · rcases free_or_host hs with hf | hh
    · exact absurd hf.toStep hn
    · obtain ⟨a, args, k, ft, id, o, hq, hf, hH, -, -, -⟩ := hh [] []
      simp only [List.append_nil] at hq
      obtain ⟨τ', o', hW, hEo⟩ := hE σ id c.store args ⟨τ, o, hH⟩
      have hst := host_step (H := (W.restrict E).host σ τ') (fits := true) (stk := []) hq hf
        ⟨hW, hEo⟩
      exact ⟨(τ', ⟨hostStore c.store o', c.frame, k.result a args o'⟩),
        sysStep_iff.mpr ⟨hl, .inr ⟨by simpa using hst, host_no_free hq⟩⟩⟩

/-- The stepper's step from a configuration that is no choice point under policy `fits`. -/
theorem stepP_of_step {H : HostSem} {fits : Bool} {c c' : Config} (h : step c = some c')
    (hu : uniqueStep fits c = true) : StepP H fits c c' := by
  cases fits with
  | false => exact step_sound h
  | true =>
    obtain ⟨d, hd⟩ := (step_sound (H := H) h).fits_total
    rwa [step_complete hd h hu] at hd

/-- A unique core step keeps the world: `SysMust` transfers back over it. -/
theorem sysMust_of_step {W : World} {fits : Bool} {Q : SysOutcome W.St → Prop} {σ : W.St}
    {c c' : Config} (hl : W.exited σ = none) (h : step c = some c')
    (hu : uniqueStep fits c = true) (hc' : SysMust W fits Q (σ, c')) :
    SysMust W fits Q (σ, c) := by
  refine .next ⟨(σ, c'), sysStep_iff.mpr ⟨hl, .inl ⟨stepP_of_step h hu, rfl⟩⟩⟩ ?_
  rintro ⟨τ, d⟩ hsys
  obtain ⟨-, hs⟩ := sysStep_iff.mp hsys
  rcases hs with ⟨hs, hτ⟩ | ⟨hs, hn⟩
  · rw [hτ, step_complete hs h hu]
    exact hc'
  · exact absurd (by rw [step_complete hs h hu]; exact step_sound h) hn

/-- A live process with a pending trap finishes abnormally, its store kept. -/
theorem sysMust_trap {W : World} {fits : Bool} {Q : SysOutcome W.St → Prop} {σ : W.St}
    {c : Config} (hl : W.exited σ = none) (ht : seqTraps c.instrs = true)
    (hQ : Q (.abnormal σ c.store)) : SysMust W fits Q (σ, c) := by
  by_cases hf : c.instrs = [.trap]
  · exact .done (sysFinal_abnormal hl hf) hQ
  · obtain ⟨c', hc'⟩ : ∃ c', Step NoHost c c' := by
      rcases seqTraps_runs c.store c.frame [] c.instrs ht with hh | ⟨s', f', es', hh⟩
      · exact False.elim (hf (seqTraps_final ht hh).2)
      · exact ⟨⟨s', f', es'⟩, by simpa using seq_step (H := NoHost) hh⟩
    obtain ⟨d, hd⟩ : ∃ d, StepP NoHost fits c d := by
      cases fits with
      | false => exact ⟨c', hc'⟩
      | true => exact hc'.fits_total
    refine .next ⟨(σ, d), sysStep_iff.mpr ⟨hl, .inl ⟨hd, rfl⟩⟩⟩ ?_
    rintro ⟨τ, d⟩ hsys
    obtain ⟨-, hs⟩ := sysStep_iff.mp hsys
    rcases hs with ⟨hs, hτ⟩ | ⟨hs, hn⟩
    · obtain ⟨hstore, -, htrap, -⟩ := step_traps hs.toStep [] (by simpa using ht)
      rw [hτ]
      exact sysMust_trap hl (by simpa using htrap) (by simpa only [hstore] using hQ)
    · rcases free_or_host hs with hf' | hh
      · exact absurd hf'.toStep hn
      · obtain ⟨a, args, k, -, -, -, hq, -⟩ := hh [] []
        simp only [List.append_nil] at hq
        rcases seqTraps_runs c.store c.frame [] c.instrs ht with hh' | ⟨s', f', es', hh'⟩
        · rw [hq] at hh'; cases hh'
        · rw [hq] at hh'; cases hh'
termination_by seqSize c.instrs
decreasing_by
  all_goals
    obtain ⟨-, -, -, hsize⟩ := step_traps hs.toStep [] (by simpa using ht)
    simpa using hsize

/-- A host-free step under policy `fits` wherever a host-free step exists. -/
theorem stepP_free {fits : Bool} {c c' : Config} (h : Step NoHost c c') :
    ∃ d, StepP NoHost fits c d := by
  cases fits with
  | false => exact ⟨c', h⟩
  | true => exact h.fits_total

/-- `must_throw` for processes, under either growth policy: a live process with a pending throw
no handler encloses finishes abnormally (uncaught), its store kept. -/
theorem sysMust_throw {W : World} {fits : Bool} {Q : SysOutcome W.St → Prop} {σ : W.St}
    {c : Config} {a : Nat} (hl : W.exited σ = none) (ht : seqThrow [] c.instrs = some (.inl a))
    (hQ : Q (.abnormal σ c.store)) : SysMust W fits Q (σ, c) := by
  by_cases hf : c.instrs = throwing a
  · exact .done (sysFinal_thrown hl hf) hQ
  · obtain ⟨c', hc'⟩ : ∃ c', Step NoHost c c' := by
      rcases seqThrow_runs c.store c.frame [] c.instrs _ ht with ⟨a', ha, hh⟩ |
        ⟨s', f', es', hh⟩
      · cases ha
        exact False.elim (hf (by simpa using seq_thrown hh))
      · exact ⟨⟨s', f', es'⟩, by simpa using seq_step (H := NoHost) hh⟩
    obtain ⟨d, hd⟩ := stepP_free (fits := fits) hc'
    refine .next ⟨(σ, d), sysStep_iff.mpr ⟨hl, .inl ⟨hd, rfl⟩⟩⟩ ?_
    rintro ⟨τ, d⟩ hsys
    obtain ⟨-, hs⟩ := sysStep_iff.mp hsys
    rcases hs with ⟨hs, hτ⟩ | ⟨hs, hn⟩
    · obtain ⟨hstore, -, -, hh⟩ := step_throw hs.toStep [] [] _ (by simpa using ht)
      rcases hh with hh | ⟨L, hL, -⟩
      · rw [hτ]
        exact sysMust_throw hl (by simpa using hh) (by simpa only [hstore] using hQ)
      · cases hL
    · rcases free_or_host hs with hf' | hh
      · exact absurd hf'.toStep hn
      · obtain ⟨a', args, k, -, -, -, hq, -⟩ := hh [] []
        simp only [List.append_nil] at hq
        rcases seqThrow_runs c.store c.frame [] c.instrs _ ht with ⟨_, _, hh'⟩ |
          ⟨s', f', es', hh'⟩
        · rw [hq] at hh'; cases hh'
        · rw [hq] at hh'; cases hh'
termination_by seqSize c.instrs
decreasing_by
  all_goals
    obtain ⟨-, -, hsize, -⟩ := step_throw hs.toStep [] [] _ (by simpa using ht)
    simpa using hsize

/-- `must_throwHandler` for processes, under either growth policy: a pending throw inside a
handler reaches that handler (`L` = the sequence with the handler's body `throwing a`) in every
execution, store, frame and world kept. -/
theorem sysMust_throwHandler {W : World} {fits : Bool} {Q : SysOutcome W.St → Prop} {σ : W.St}
    {c : Config} {L : List AInstr} (hl : W.exited σ = none)
    (ht : seqThrow [] c.instrs = some (.inr L))
    (hL : SysMust W fits Q (σ, ⟨c.store, c.frame, L⟩)) : SysMust W fits Q (σ, c) := by
  obtain ⟨c', hc'⟩ : ∃ c', Step NoHost c c' := by
    rcases seqThrow_runs c.store c.frame [] c.instrs _ ht with ⟨a', ha, -⟩ | ⟨s', f', es', hh⟩
    · cases ha
    · exact ⟨⟨s', f', es'⟩, by simpa using seq_step (H := NoHost) hh⟩
  obtain ⟨d, hd⟩ := stepP_free (fits := fits) hc'
  refine .next ⟨(σ, d), sysStep_iff.mpr ⟨hl, .inl ⟨hd, rfl⟩⟩⟩ ?_
  rintro ⟨τ, d⟩ hsys
  obtain ⟨-, hs⟩ := sysStep_iff.mp hsys
  rcases hs with ⟨hs, hτ⟩ | ⟨hs, hn⟩
  · obtain ⟨hstore, hframe, -, hh⟩ := step_throw hs.toStep [] [] _ (by simpa using ht)
    rw [hτ]
    rcases hh with hh | ⟨L', hL', hl'⟩
    · exact sysMust_throwHandler hl (by simpa using hh) (by simpa only [hstore, hframe] using hL)
    · cases hL'
      simp only [List.reverse_nil, List.map_nil, List.nil_append, List.append_nil] at hl'
      obtain ⟨s', f', es'⟩ := d
      dsimp only at hstore hframe hl'
      subst hstore hframe hl'
      exact hL
  · rcases free_or_host hs with hf' | hh
    · exact absurd hf'.toStep hn
    · obtain ⟨a', args, k, -, -, -, hq, -⟩ := hh [] []
      simp only [List.append_nil] at hq
      rcases seqThrow_runs c.store c.frame [] c.instrs _ ht with ⟨_, hr, -⟩ | ⟨s', f', es', hh'⟩
      · cases hr
      · rw [hq] at hh'; cases hh'
termination_by seqSize c.instrs
decreasing_by
  all_goals
    obtain ⟨-, -, hsize, -⟩ := step_throw hs.toStep [] [] _ (by simpa using ht)
    simpa using hsize

/-- `runDet_must` for processes, under either growth policy: a live process whose deterministic
run (unique steps, trap propagation, throw normalization through caught throws) reaches `c'`
satisfies `SysMust` when every way `c'` finishes satisfies `Q`. -/
theorem sysMust_of_runDet {W : World} {fits : Bool} {Q : SysOutcome W.St → Prop} {σ : W.St}
    {n : Nat} {c c' : Config} (hl : W.exited σ = none) (h : runDet n c = some c')
    (hQ : ∀ o, SysFinal W (σ, c') o → Q o) : SysMust W fits Q (σ, c) := by
  induction n generalizing c with
  | zero => simp only [runDet, reduceCtorEq] at h
  | succ n ih =>
    cases ht : seqTraps c.instrs with
    | true =>
      simp only [runDet, ht, Bool.cond_true] at h
      cases Option.some.inj h
      exact sysMust_trap hl ht (hQ _ (sysFinal_abnormal hl rfl))
    | false =>
      simp only [runDet, ht, Bool.cond_false] at h
      cases hth : seqThrow [] c.instrs with
      | some r =>
        cases r with
        | inl a =>
          simp only [hth] at h
          cases Option.some.inj h
          exact sysMust_throw hl hth (hQ _ (sysFinal_thrown hl rfl))
        | inr L =>
          simp only [hth] at h
          exact sysMust_throwHandler hl hth (ih h)
      | none =>
        simp only [hth] at h
        cases hu : uniqueStep false c with
        | false => simp only [hu, Bool.cond_false, reduceCtorEq] at h
        | true =>
          simp only [hu, Bool.cond_true] at h
          cases hs : seq c.store c.frame [] c.instrs with
          | step s f es =>
            simp only [hs] at h
            exact sysMust_of_step hl (by simp only [step, hs]) (uniqueStep_le fits hu) (ih h)
          | final =>
            simp only [hs] at h
            have he := Option.some.inj h
            subst c'
            rcases seq_final hs with ⟨_, htrap⟩ | ⟨vs, hvals⟩
            · exact .done (sysFinal_abnormal hl htrap) (hQ _ (sysFinal_abnormal hl htrap))
            · have hv : c.instrs = vals vs := by simpa using hvals
              exact .done (sysFinal_returned hl hv) (hQ _ (sysFinal_returned hl hv))
          | _ => simp only [hs, reduceCtorEq] at h

/-- A live process whose configuration holds only values has returned them. -/
theorem sysMust_returned {W : World} {fits : Bool} {Q : SysOutcome W.St → Prop} {σ : W.St}
    {c : Config} {vs : List Val} (hl : W.exited σ = none) (hv : c.instrs = vals vs)
    (hQ : Q (.returned σ c.store vs)) : SysMust W fits Q (σ, c) :=
  .done (sysFinal_returned hl hv) hQ

/-- An exited process has finished with its exit code. -/
theorem sysMust_exited {W : World} {fits : Bool} {Q : SysOutcome W.St → Prop} {σ : W.St}
    {c : Config} {k : Nat} (he : W.exited σ = some k) (hQ : Q (.exited σ c.store k)) :
    SysMust W fits Q (σ, c) :=
  .done (sysFinal_exited he) hQ

/-- A host call satisfies `SysMust` once it has an allowed outcome and every allowed outcome's
continuation does. -/
theorem sysMust_host {W : World} {fits : Bool} {Q : SysOutcome W.St → Prop} {σ : W.St}
    {c : Config} {a : Nat} {args : List Val} {k : HCtx} {dt : DefType} {id : Nat}
    (hq : seq c.store c.frame [] c.instrs = .host a args k)
    (hf : c.store.funcs[a]? = some (.host dt id)) (hl : W.exited σ = none)
    (hex : ∃ τ o, W.host σ τ id c.store args o)
    (hall : ∀ τ o, W.host σ τ id c.store args o →
      SysMust W fits Q (τ, ⟨hostStore c.store o, c.frame, k.result a args o⟩)) :
    SysMust W fits Q (σ, c) := by
  obtain ⟨τ, o, ho⟩ := hex
  have hst := host_step (fits := fits) (stk := []) hq hf ho
  refine .next ⟨(τ, _), sysStep_iff.mpr ⟨hl, .inr ⟨by simpa using hst, host_no_free hq⟩⟩⟩ ?_
  rintro ⟨τ', d⟩ hsys
  obtain ⟨-, hs⟩ := sysStep_iff.mp hsys
  rcases hs with ⟨hs, -⟩ | ⟨hs, -⟩
  · exact absurd hs (host_no_free hq)
  · obtain ⟨ft', id', o', hf', hH, hds, hdf, hdi⟩ :=
      host_complete hs [] [] a args k (by simpa using hq)
    rw [hf] at hf'
    simp only [Option.some.injEq, FuncInst.host.injEq] at hf'
    obtain ⟨rfl, rfl⟩ := hf'
    have hd : d = ⟨hostStore c.store o', c.frame, k.result a args o'⟩ := by
      rcases d with ⟨ds, df, di⟩
      simp only [List.reverse_nil, vals, List.map_nil, List.nil_append, List.append_nil] at hdi
      simp only at hds hdf
      rw [hds, hdf, hdi]
    rw [hd]
    exact hall τ' o' hH

/-- An allowed divergence of a live host call refutes `SysMust`: the call stays, its world
too. -/
theorem host_diverged_not_must {W : World} {fits : Bool} {Q : SysOutcome W.St → Prop}
    {σ τ : W.St} {c : Config} {a : Nat} {args : List Val} {k : HCtx} {dt : DefType} {id : Nat}
    (hq : seq c.store c.frame [] c.instrs = .host a args k)
    (hf : c.store.funcs[a]? = some (.host dt id)) (hl : W.exited σ = none)
    (hd : W.host σ τ id c.store args .diverged) : ¬ SysMust W fits Q (σ, c) := by
  rw [W.stay hd] at hd
  have hst := host_step (fits := fits) (stk := []) hq hf hd
  have hx := seq_explains NoHost c.store c.frame [] c.instrs
  rw [hq] at hx
  obtain ⟨_, _, _, _, _, _, hes⟩ := hx
  have hself : SysStep W fits (σ, c) (σ, c) := by
    refine sysStep_iff.mpr ⟨hl, .inr ⟨?_, host_no_free hq⟩⟩
    simpa [hostStore, HCtx.result, ← hes] using hst
  intro h
  generalize hx : (σ, c) = x at h
  induction h with
  | done hfin _ =>
    subst hx
    exact sysFinal_no_step hfin hself
  | next _ _ ih =>
    subst hx
    exact ih _ hself rfl

end FVA.Wasm.Exec
