import FVA.Proof.Lib.Walk
import FVA.Spec.CAbi

/-!
# Fresh instances of lifted modules (U8 L2)

A module without imports, globals, element/data segments or start function, whose tables start
null, has one fresh instance: its allocation in the empty store with null table elements, since
nothing but `ref.null` runs during instantiation. Claims
quantify over every instance (`Instance`), so a proof first fixes it with `instance_alloc`, then
evaluates the allocation (`rfl`/`decide`) to find each export's function.
-/

namespace FVA.Wasm.Exec

open FVA.Wasm FVA.Wasm.Exec.Ref

/-- No step starts from an empty instruction sequence. -/
theorem no_step_nil {H : HostSem} {s : Store} {f : Frame} {c : Config} :
    ¬ Step H ⟨s, f, []⟩ c := by
  intro h
  have := seq_complete h [] [] (by simp [seqUnique])
  simp [seq] at this

/-- Executions from an empty instruction sequence go nowhere. -/
theorem steps_nil {H : HostSem} {s : Store} {f : Frame} {c : Config}
    (h : Steps H ⟨s, f, []⟩ c) : c = ⟨s, f, []⟩ := by
  cases h.cases_head with
  | inl he => exact he.symm
  | inr hs => obtain ⟨_, hs, _⟩ := hs; exact absurd hs no_step_nil

theorem nullTables_init {m : Module} (h : m.nullTables = true) {t : Table} (ht : t ∈ m.tables) :
    ∃ h, t.init = [.refNull h] := by
  have hi := List.all_eq_true.mp h t ht
  split at hi
  · exact ⟨_, ‹_›⟩
  · cases hi

/-- `ref.null` evaluates to the null reference: its only step reaches the value. -/
theorem steps_refNull {H : HostSem} {s : Store} {f : Frame} {h : HeapType} {r : Ref}
    (hs : Steps H ⟨s, f, [.plain (.refNull h)]⟩ ⟨s, f, [(Val.ref r).instr]⟩) : r = .null := by
  rcases hs.cases_head with hc | ⟨mid, h₀, hrest⟩
  · cases r <;> simp [Val.instr] at hc
  · have hst : step ⟨s, f, [.plain (.refNull h)]⟩ = some ⟨s, f, [(Val.ref .null).instr]⟩ := by
      simp [step, seq, toVal, atInstr, instrStep, Val.instr]
    have hmid := step_complete h₀ hst
      (by simp [uniqueStep, seqUnique, toVal, atUnique, instrUnique])
    subst hmid
    have hv := congrArg Config.instrs (steps_values (vs := [.ref .null]) hrest)
    have he := congrArg toVal (List.singleton_inj.mp hv)
    simpa [toVal_instr] using he

theorem forall₂_const {α β : Type} {R : α → β → Prop} {c : β} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → (∀ x ∈ xs, ∀ y, R x y → y = c) →
      ys = xs.map fun _ => c
  | [], [], .nil, _ => rfl
  | x :: xs, y :: ys, .cons hxy h, hc => by
    rw [List.map_cons, hc x (by simp) y hxy, forall₂_const h fun x' hx' => hc x' (by simp [hx'])]

/-- The tables' initializers, each a `ref.null`, evaluate to null. -/
theorem nullTables_steps {m : Module} (h : m.nullTables = true) (H : HostSem) (s : Store)
    (f : Frame) :
    List.Forall₂ (fun t r => Steps H ⟨s, f, t.init.map .plain⟩ ⟨s, f, [(Val.ref r).instr]⟩)
      m.tables (m.tables.map fun _ => .null) := by
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro t ht
  obtain ⟨_, hi⟩ := nullTables_init h ht
  rw [hi]
  exact .single StepP.refNull

/-- A fresh instance of a module without globals, segments or start function, whose tables start
null, is its allocation in the empty store (a fresh instance has no imports by definition). -/
theorem instance_alloc {m : Module} {H : HostSem} {s : Store} {inst : ModuleInst}
    (hg : m.globals = []) (ht : m.nullTables = true) (he : m.elems = []) (hd : m.datas = [])
    (hs : m.start = none) (h : Instance m H s inst) :
    (s, inst) = allocModule {} m [] [] (m.tables.map fun _ => .null) [] := by
  obtain ⟨_, gvals, trefs, erefs, s₁, ha, hgv, htr, her, hrun⟩ := h
  rw [hg] at hgv
  rw [he] at her
  cases hgv
  cases her
  have htrefs : trefs = m.tables.map fun _ => .null :=
    forall₂_const htr fun t ht' r hr => by
      obtain ⟨_, hi⟩ := nullTables_init ht ht'
      rw [hi] at hr
      exact steps_refNull hr
  subst htrefs
  have hc : initCode m = [] := by simp [initCode, he, hd, hs]
  rw [hc, List.map_nil] at hrun
  have := steps_nil hrun
  simp only [Config.mk.injEq] at this
  rw [this.1, ← ha]

/-- The canonical fresh instance of a module without imports, globals, segments or start
function, whose tables start null: its allocation in the empty store. Exposes the witness
`instantiable_alloc` hides, so a `Prepared` existence clause can name it. -/
theorem instance_alloc_self {m : Module} (H : HostSem) (hi : m.imports = [])
    (hg : m.globals = []) (ht : m.nullTables = true) (he : m.elems = []) (hd : m.datas = [])
    (hs : m.start = none) :
    Instance m H (allocModule {} m [] [] (m.tables.map fun _ => .null) []).1
      (allocModule {} m [] [] (m.tables.map fun _ => .null) []).2 := by
  have hc : initCode m = [] := by simp [initCode, he, hd, hs]
  refine ⟨by simp [ImportsMatch, hi], [], m.tables.map fun _ => .null, [],
    (allocModule {} m [] [] (m.tables.map fun _ => .null) []).1, rfl, ?_,
    nullTables_steps ht H _ _, ?_, ?_⟩
  · rw [hg]; exact .nil
  · rw [he]; exact .nil
  · rw [hc, List.map_nil]

/-- A module without imports, globals, segments or start function, whose tables start null, is
instantiable: its allocation in the empty store is a fresh instance. -/
theorem instantiable_alloc {m : Module} (hi : m.imports = []) (hg : m.globals = [])
    (ht : m.nullTables = true) (he : m.elems = []) (hd : m.datas = []) (hs : m.start = none) :
    Instantiable m :=
  fun H => ⟨_, _, instance_alloc_self H hi hg ht he hd hs⟩

/-- `Must` is monotone in its postcondition. -/
theorem Must.mono {H : HostSem} {Q Q' : Outcome → Prop} {c : Config} (h : Must H Q c)
    (hq : ∀ o, Q o → Q' o) : Must H Q' c := by
  induction h with
  | done hf hq' => exact .done hf (hq _ hq')
  | next hs _ ih => exact .next hs ih

/-- A deterministic run that ends returning `vs` in store `s'` proves the call returns: the shape
`CallReturns` asks of the invoke configuration. -/
theorem must_returned_of_runDet {H : HostSem} {P : Store → List Val → Prop} {n : Nat}
    {c : Config} {s' : Store} {f' : Frame} {vs : List Val}
    (hr : runDet n c = some ⟨s', f', vals vs⟩) (hp : P s' vs) :
    Must H (fun | .returned s vs => P s vs | _ => False) c := by
  refine runDet_must hr ?_
  rintro (⟨s'', ws⟩ | s'' | ⟨s'', a⟩) ⟨hs, hv⟩
  · simp only at hs hv
    obtain rfl := vals_inj.mp hv.symm
    subst hs
    exact hp
  · exact absurd hv (vals_ne_trap vs)
  · exact absurd hv (vals_ne_throwing vs a)

/-- A deterministic run whose final configuration (reached by `runDet`, kept as `Option.get` so
the kernel can evaluate it) returns `vs` with a final store satisfying `P` proves the call
returns. Lets a long run close by `decide +kernel` on the concrete final configuration, without
writing the store out. -/
theorem must_returned_of_runDet_get {H : HostSem} {P : Store → List Val → Prop} {n : Nat}
    {c : Config} {vs : List Val} (hsome : (runDet n c).isSome)
    (hi : ((runDet n c).get hsome).instrs = vals vs)
    (hp : P ((runDet n c).get hsome).store vs) :
    Must H (fun | .returned s vs' => vs' = vs ∧ P s vs' | _ => False) c := by
  refine runDet_must (Option.some_get hsome).symm ?_
  rintro (⟨s'', ws⟩ | s'' | ⟨s'', a⟩) ⟨hs, hv⟩
  · obtain rfl := vals_inj.mp (hv.symm.trans hi)
    subst hs
    exact ⟨rfl, hp⟩
  · exact absurd (hi.symm.trans hv) (vals_ne_trap vs)
  · exact absurd (hi.symm.trans hv) (vals_ne_throwing vs a)

/-- The trap analogue of `must_returned_of_runDet_get`: a deterministic run that ends in a trap,
with a final store satisfying `P`, proves the call traps. -/
theorem must_trapped_of_runDet_get {H : HostSem} {P : Store → Prop} {n : Nat}
    {c : Config} (hsome : (runDet n c).isSome)
    (hi : ((runDet n c).get hsome).instrs = [.trap])
    (hp : P ((runDet n c).get hsome).store) :
    Must H (fun | .trapped s => P s | _ => False) c := by
  refine runDet_must (Option.some_get hsome).symm ?_
  rintro (⟨s'', ws⟩ | s'' | ⟨s'', a⟩) ⟨hs, hv⟩
  · exact absurd (hv.symm.trans hi) (vals_ne_trap ws)
  · subst hs
    exact hp
  · exact absurd (hv.symm.trans hi) (by simp [throwing])

end FVA.Wasm.Exec
