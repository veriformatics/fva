import FVATest.Subjects.Lz4C.Lifted
import FVA.Proof.Lib.Instance

/-! Every fresh instance of `lz4-c.wasm` is one store: the stack-pointer global starts at 65536
and the data segment (lz4's `inc32table`/`dec64table`, 64 bytes at 65536) is copied in by a
deterministic run (proof support; outside the review surface). -/

namespace Subjects.Lz4C

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

set_option maxRecDepth 100000

/-- The allocation in the empty store, before initialization. -/
noncomputable def alloc : Store × ModuleInst :=
  allocModule {} Lifted.module [] [.i32 65536] []

/-- The initialization run: the data segment's `memory.init` + `data.drop`. -/
noncomputable def initConfig : Config :=
  ⟨alloc.1, ⟨[], alloc.2⟩, (initCode Lifted.module).map .plain⟩

attribute [local irreducible] alloc in
theorem init_some : (runDet 1000 initConfig).isSome := by decide +kernel

/-- The store every fresh instance has. -/
noncomputable def store0 : Store := ((runDet 1000 initConfig).get init_some).store

theorem init_instrs : ((runDet 1000 initConfig).get init_some).instrs = vals [] := by
  kernel_rfl

theorem init_must (H : HostSem) :
    Must H (fun o => o = .returned store0 []) initConfig := by
  refine runDet_must (Option.some_get init_some).symm ?_
  rintro (⟨s, vs⟩ | s) ⟨hs, hv⟩
  · rw [init_instrs] at hv
    obtain rfl := vals_inj.mp hv.symm
    rw [← hs]; rfl
  · rw [init_instrs] at hv
    exact absurd hv (vals_ne_trap [])

/-- A deterministic run ending in values is an execution. -/
theorem steps_of_runDet {H : HostSem} {n : Nat} {c c' : Config} {vs : List Val}
    (hr : runDet n c = some c') (hv : c'.instrs = vals vs) : Steps H c c' := by
  induction n generalizing c with
  | zero => simp only [runDet, reduceCtorEq] at hr
  | succ n ih =>
    cases ht : seqTraps c.instrs with
    | true =>
      simp only [runDet, ht, Bool.cond_true] at hr
      have hi := congrArg (fun x => x.instrs) (Option.some.inj hr)
      exact False.elim ((vals_ne_trap vs) (hv.symm.trans hi.symm))
    | false =>
      simp only [runDet, ht, Bool.cond_false] at hr
      cases hu : uniqueStep c with
      | false => simp only [hu, Bool.cond_false, reduceCtorEq] at hr
      | true =>
        simp only [hu, Bool.cond_true] at hr
        cases hs : seq c.store c.frame [] c.instrs with
        | step s f es =>
          simp only [hs] at hr
          exact Relation.ReflTransGen.head (step_sound (by simp only [step, hs])) (ih hr)
        | final =>
          simp only [hs] at hr
          cases Option.some.inj hr
          exact .refl
        | _ => simp only [hs, reduceCtorEq] at hr

attribute [local irreducible] alloc initConfig in
theorem init_run : runDet 1000 initConfig = some ⟨store0, ⟨[], alloc.2⟩, []⟩ := by
  have hf : ((runDet 1000 initConfig).get init_some).frame = ⟨[], alloc.2⟩ := by kernel_rfl
  exact (Option.some_get init_some).symm.trans (congrArg some
    ((congrArg (fun f => Config.mk store0 f ((runDet 1000 initConfig).get init_some).instrs)
      hf).trans (congrArg (fun es => Config.mk store0 ⟨[], alloc.2⟩ es) init_instrs)))

/-- `(store0, alloc.2)` is a fresh instance. -/
theorem instance_store0 (H : HostSem) : Instance Lifted.module H store0 alloc.2 := by
  refine ⟨?_, [.i32 65536], [], alloc.1, rfl, ?_, ?_, ?_⟩
  · exact .nil
  · exact .cons .refl .nil
  · exact .nil
  · exact steps_of_runDet (vs := []) init_run rfl

/-- Every fresh instance is `(store0, alloc.2)`. -/
theorem instance_eq {H : HostSem} {s : Store} {inst : ModuleInst}
    (h : Instance Lifted.module H s inst) : s = store0 ∧ inst = alloc.2 := by
  obtain ⟨-, gvals, erefs, s₁, halloc, hg, he, hinit⟩ := h
  obtain ⟨v, rfl⟩ : ∃ v, gvals = [v] := by
    cases hg with
    | cons _ hn => cases hn; exact ⟨_, rfl⟩
  have hv : v = .i32 65536 := by
    obtain ⟨hstep, -⟩ := List.forall₂_cons.mp hg
    have hc := Ref.steps_values (H := H) (vs := [.i32 65536])
      (show Steps H ⟨s₁, ⟨[], inst⟩, vals [.i32 65536]⟩ ⟨s₁, ⟨[], inst⟩, [v.instr]⟩ from hstep)
    exact Val.instr_inj.mp (List.singleton_inj.mp (congrArg Config.instrs hc))
  subst hv
  obtain rfl : erefs = [] := by cases he; rfl
  have hai : (s₁, inst) = alloc := halloc.symm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hai
  have ho := (init_must H).outcome hinit (o := .returned s []) ⟨rfl, rfl⟩
  exact ⟨(Outcome.returned.inj ho).1, rfl⟩

end Subjects.Lz4C
