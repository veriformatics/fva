import FVATest.Subjects.Lz4C.Numeric
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
  allocModule {} Lifted.module [] [.i32 65536] [] []

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
  rintro (⟨s, vs⟩ | s | ⟨s, a⟩) ⟨hs, hv⟩
  · rw [init_instrs] at hv
    obtain rfl := vals_inj.mp hv.symm
    rw [← hs]; rfl
  · rw [init_instrs] at hv
    exact absurd hv (vals_ne_trap [])
  · rw [init_instrs] at hv
    exact absurd hv (vals_ne_throwing [] a)

attribute [local irreducible] alloc initConfig in
theorem init_run : runDet 1000 initConfig = some ⟨store0, ⟨[], alloc.2⟩, []⟩ := by
  have hf : ((runDet 1000 initConfig).get init_some).frame = ⟨[], alloc.2⟩ := by kernel_rfl
  exact (Option.some_get init_some).symm.trans (congrArg some
    ((congrArg (fun f => Config.mk store0 f ((runDet 1000 initConfig).get init_some).instrs)
      hf).trans (congrArg (fun es => Config.mk store0 ⟨[], alloc.2⟩ es) init_instrs)))

/-- `(store0, alloc.2)` is a fresh instance. -/
theorem instance_store0 (H : HostSem) : Instance Lifted.module H store0 alloc.2 := by
  refine ⟨?_, [.i32 65536], [], [], alloc.1, rfl, ?_, ?_, ?_, ?_⟩
  · exact .nil
  · exact .cons .refl .nil
  · exact .nil
  · exact .nil
  · exact runDet_steps init_run

/-- Every fresh instance is `(store0, alloc.2)`. -/
theorem instance_eq {H : HostSem} {s : Store} {inst : ModuleInst}
    (h : Instance Lifted.module H s inst) : s = store0 ∧ inst = alloc.2 := by
  obtain ⟨-, gvals, trefs, erefs, s₁, halloc, hg, ht, he, hinit⟩ := h
  obtain ⟨v, rfl⟩ : ∃ v, gvals = [v] := by
    cases hg with
    | cons _ hn => cases hn; exact ⟨_, rfl⟩
  have hv : v = .i32 65536 := by
    obtain ⟨hstep, -⟩ := List.forall₂_cons.mp hg
    have hc := Ref.steps_values (H := H) (vs := [.i32 65536])
      (show Steps H ⟨s₁, ⟨[], inst⟩, vals [.i32 65536]⟩ ⟨s₁, ⟨[], inst⟩, [v.instr]⟩ from hstep)
    exact Val.instr_inj.mp (List.singleton_inj.mp (congrArg Config.instrs hc))
  subst hv
  obtain rfl : trefs = [] := by cases ht; rfl
  obtain rfl : erefs = [] := by cases he; rfl
  have hai : (s₁, inst) = alloc := halloc.symm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hai
  have ho := (init_must H).outcome hinit (o := .returned s []) ⟨rfl, rfl⟩
  exact ⟨(Outcome.returned.inj ho).1, rfl⟩

end Subjects.Lz4C
