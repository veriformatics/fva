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

end FVA.Wasm.Exec
