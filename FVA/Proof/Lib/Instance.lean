import FVA.Proof.Lib.Walk
import FVA.Spec.CAbi

/-!
# Fresh instances of lifted modules (U8 L2)

A module without imports, globals, element/data segments or start function has one fresh
instance: its allocation in the empty store, since nothing runs during instantiation. Claims
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

/-- A fresh instance of a module without globals, segments or start function is its allocation in
the empty store (a fresh instance has no imports by definition). -/
theorem instance_alloc {m : Module} {H : HostSem} {s : Store} {inst : ModuleInst}
    (hg : m.globals = []) (he : m.elems = []) (hd : m.datas = [])
    (hs : m.start = none) (h : Instance m H s inst) : (s, inst) = allocModule {} m [] [] [] := by
  obtain ⟨_, gvals, erefs, s₁, ha, hgv, her, hrun⟩ := h
  rw [hg] at hgv
  rw [he] at her
  cases hgv
  cases her
  have hc : initCode m = [] := by simp [initCode, he, hd, hs]
  rw [hc, List.map_nil] at hrun
  have := steps_nil hrun
  simp only [Config.mk.injEq] at this
  rw [this.1, ← ha]

/-- A module without imports, globals, segments or start function is instantiable: its
allocation in the empty store is a fresh instance. -/
theorem instantiable_alloc {m : Module} (hi : m.imports = []) (hg : m.globals = [])
    (he : m.elems = []) (hd : m.datas = []) (hs : m.start = none) : Instantiable m := by
  intro H
  have hc : initCode m = [] := by simp [initCode, he, hd, hs]
  let a := allocModule {} m [] [] []
  refine ⟨a.1, a.2, by simp [ImportsMatch, hi], [], [], a.1, rfl, ?_, ?_, ?_⟩
  · rw [hg]; exact .nil
  · rw [he]; exact .nil
  · rw [hc, List.map_nil]

/-- The canonical fresh instance of a module without imports, globals, segments or start
function: its allocation in the empty store. Exposes the witness `instantiable_alloc` hides, so a
`Prepared` existence clause can name it. -/
theorem instance_alloc_self {m : Module} (H : HostSem) (hi : m.imports = [])
    (hg : m.globals = []) (he : m.elems = []) (hd : m.datas = []) (hs : m.start = none) :
    Instance m H (allocModule {} m [] [] []).1 (allocModule {} m [] [] []).2 := by
  have hc : initCode m = [] := by simp [initCode, he, hd, hs]
  refine ⟨by simp [ImportsMatch, hi], [], [], (allocModule {} m [] [] []).1, rfl, ?_, ?_, ?_⟩
  · rw [hg]; exact .nil
  · rw [he]; exact .nil
  · rw [hc, List.map_nil]

theorem vals_inj {vs ws : List Val} : vals vs = vals ws ↔ vs = ws := by
  constructor
  · intro h
    exact List.map_injective_iff.mpr (fun _ _ h => Val.instr_inj.mp h) h
  · rintro rfl; rfl

theorem vals_ne_trap (vs : List Val) : vals vs ≠ [.trap] := by
  rcases vs with _ | ⟨v, vs⟩
  · simp [vals]
  · intro h
    have := congrArg List.head? h
    simp only [vals, List.map_cons, List.head?_cons, Option.some.injEq] at this
    have hv := congrArg toVal this
    rw [toVal_instr, toVal_trap] at hv
    cases hv

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
    Must H (fun | .returned s vs => P s vs | .trapped _ => False) c := by
  refine runDet_must hr ?_
  rintro (⟨s'', ws⟩ | s'') ⟨hs, hv⟩
  · simp only at hs hv
    obtain rfl := vals_inj.mp hv.symm
    subst hs
    exact hp
  · exact absurd hv (vals_ne_trap vs)

/-- A deterministic run whose final configuration (reached by `runDet`, kept as `Option.get` so
the kernel can evaluate it) returns `vs` with a final store satisfying `P` proves the call
returns. Lets a long run close by `decide +kernel` on the concrete final configuration, without
writing the store out. -/
theorem must_returned_of_runDet_get {H : HostSem} {P : Store → List Val → Prop} {n : Nat}
    {c : Config} {vs : List Val} (hsome : (runDet n c).isSome)
    (hi : ((runDet n c).get hsome).instrs = vals vs)
    (hp : P ((runDet n c).get hsome).store vs) :
    Must H (fun | .returned s vs' => vs' = vs ∧ P s vs' | .trapped _ => False) c := by
  refine runDet_must (Option.some_get hsome).symm ?_
  rintro (⟨s'', ws⟩ | s'') ⟨hs, hv⟩
  · obtain rfl := vals_inj.mp (hv.symm.trans hi)
    subst hs
    exact ⟨rfl, hp⟩
  · exact absurd (hi.symm.trans hv) (vals_ne_trap vs)

/-- The trap analogue of `must_returned_of_runDet_get`: a deterministic run that ends in a trap,
with a final store satisfying `P`, proves the call traps. -/
theorem must_trapped_of_runDet_get {H : HostSem} {P : Store → Prop} {n : Nat}
    {c : Config} (hsome : (runDet n c).isSome)
    (hi : ((runDet n c).get hsome).instrs = [.trap])
    (hp : P ((runDet n c).get hsome).store) :
    Must H (fun | .returned _ _ => False | .trapped s => P s) c := by
  refine runDet_must (Option.some_get hsome).symm ?_
  rintro (⟨s'', ws⟩ | s'') ⟨hs, hv⟩
  · exact absurd (hv.symm.trans hi) (vals_ne_trap ws)
  · subst hs
    exact hp

end FVA.Wasm.Exec
