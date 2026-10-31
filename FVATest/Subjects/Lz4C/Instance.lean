import FVATest.Subjects.Lz4C.Lifted
import FVA.Proof.Lib.Instance

/-! Every fresh instance of `lz4-c.wasm` is one store: the stack-pointer global starts at 65536
and the data segment (lz4's `inc32table`/`dec64table`, 60 bytes at 65536) is copied in by a
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
