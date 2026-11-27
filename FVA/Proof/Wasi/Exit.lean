import FVA.Proof.Wasi.Canonical
import FVA.Proof.Wasi.Launch

/-!
# The first system claim under `E` (U29b T4, T4′)

T4: U29a's minimal command (`_start` = `proc_exit 0`) launches, and every launch exits with
status 0 under `E` from every live world: T3 fixes the launch to the machine's instantiation,
the machine runs to the `proc_exit` call, T1's host answers it, and `machineRun_sysMust`
(through `launch_sysMust`) carries the exit back to the start. T4′: with every call's divergence
allowed, the same start satisfies no total-correctness claim — T4 rests on `E`'s progress clause.
-/

namespace FVA.Wasi.LaunchExample

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Machine FVA.Wasi

theorem cmd_instU : (instantiateU 100 (hostMStore cmd) cmd (hostImports cmd)).isSome = true := by
  decide

/-- The machine store + instance every launch of `cmd` starts from. -/
def cmdInst : MStore × ModuleInst :=
  (instantiateU 100 (hostMStore cmd) cmd (hostImports cmd)).get cmd_instU

theorem cmdInst_eq : instantiateU 100 (hostMStore cmd) cmd (hostImports cmd) = some cmdInst := by
  simp [cmdInst]

theorem cmd_start : cmdInst.2.exportFunc "_start" = some 2 := by decide

theorem cmd_mem : cmdInst.2.exportMem "memory" = some 0 := by decide

/-- The launch on the machine. -/
def m₀ : MState := MState.ofInvoke cmdInst.1 2 []

/-- The machine at the `proc_exit` call. -/
def m₁ : MState := (m₀.runU true 8).1

theorem seg : m₀.runU true 8 = (m₁, false) := Prod.ext rfl (by decide)

theorem m₁_call : m₁.hostCall = some (1, 1, []) := rfl

/-- The three unique steps from the launch to the `proc_exit` call. -/
theorem steps₀ : ∃ ma mb, m₀.step = some ma ∧ ma.step = some mb ∧ mb.step = some m₁ ∧
    m₀.uniq true = true ∧ ma.uniq true = true ∧ mb.uniq true = true :=
  ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem m₁_args : (m₁.stack.take 1).reverse = [.i32 0] := rfl

theorem m₁_mem : ∃ mm, m₁.store.mems[0]? = some mm := ⟨_, rfl⟩

/-- The driver's step at the `proc_exit` call (`answerHost`): the exit recorded, the call
traps. -/
theorem cmd_answer (σ₀ : State) : answerHost (wasiHost cmd 0 none) (σ₀, m₁) =
    some ({ σ₀ with exited := some 0 }, m₁.hostResume m₁.store [.trap] [] 1) := by
  obtain ⟨mm, hmm⟩ := m₁_mem
  have hX := wasiHost_procExit (rand := none) (σ := σ₀) (k := 0) cmd_bind.2 hmm
  rw [← m₁_args] at hX
  simp [answerHost, m₁_call, hX, MHostOut.out]

/-- T4: the command launches; every launch exits with status 0 under `E` from every live world. -/
theorem cmd_exits_zero :
    (∃ c mem, Launch cmd "_start" [] c mem) ∧
      ∀ c mem, Launch cmd "_start" [] c mem → ∀ σ₀ : State, σ₀.exited = none →
        SysMust ((world cmd mem).restrict (E cmd mem)) true
          (fun o => ∃ τ s, o = .exited τ s 0) (σ₀, c) := by
  refine ⟨cmd_launch, fun c mem hl σ₀ he => ?_⟩
  obtain ⟨i, hi⟩ := sysRun_runU (X := wasiHost cmd 0 none) he 8 seg
  obtain ⟨mm, hmm⟩ := m₁_mem
  have hX : wasiHost cmd 0 none σ₀ 1 m₁.store (m₁.stack.take 1).reverse =
      some ({ σ₀ with exited := some 0 }, m₁.store, .trapped) := by
    rw [m₁_args]
    exact wasiHost_procExit (k := 0) cmd_bind.2 hmm
  have hrun : sysRun State.exited (wasiHost cmd 0 none) (i + 2) (σ₀, m₀) =
      ({ σ₀ with exited := some 0 }, m₁.hostResume m₁.store [.trap] [] 1, false) := by
    rw [hi 2]
    simp [sysRun, he, m₁_call, hX, MHostOut.out]
  exact launch_sysMust cmdInst_eq cmd_start cmd_mem hrun (sysMust_exited rfl ⟨_, _, rfl⟩) c mem hl

/-- `E` with every call's divergence allowed (T4′). -/
def Ediv (σ τ : State) : HostSem := fun id s vs o =>
  E cmd 0 σ τ id s vs o ∨ (τ = σ ∧ o = .diverged)

/-- T4′: with divergence allowed the launch satisfies no total-correctness claim (the run reaches
the `proc_exit` call, which may block). -/
theorem cmd_needs_progress (σ₀ : State) (he : σ₀.exited = none) (Q : SysOutcome State → Prop) :
    ¬ SysMust ((world cmd 0).restrict Ediv) true Q (σ₀, invokeConfig cmdInst.1.abs 2 []) := by
  intro hm
  have hi₀ : m₀.Inv := instantiateU_inv (hostMStore_inv cmd) (mems_fit cmd_valid) cmdInst_eq
  have he' : ((world cmd 0).restrict Ediv).exited σ₀ = none := he
  rw [← abs_ofInvoke] at hm
  obtain ⟨ma, mb, h₁, h₂, h₃, hu₀, hu₁, hu₂⟩ := steps₀
  have hi₁ := (step_sim hi₀ h₁).1
  have hi₂ := (step_sim hi₁ h₂).1
  have hm₃ := sysMust_forward_uniq he' hi₂ hu₂ h₃
    (sysMust_forward_uniq he' hi₁ hu₁ h₂ (sysMust_forward_uniq he' hi₀ hu₀ h₁ hm))
  obtain ⟨a, dt, ft, hc, hfn, hft, hk1, hk⟩ := hostCall_some m₁_call
  obtain ⟨K, hq, -⟩ := abs_host hc hfn hft (by rw [← hk1]; exact hk)
  have hfa : m₁.abs.store.funcs[a]? = some (.host dt 1) := hfn
  have hW : ((world cmd 0).restrict Ediv).host σ₀ σ₀ 1 m₁.abs.store
      (m₁.stack.take ft.params.length).reverse .diverged := by
    refine ⟨?_, ?_⟩
    · show (world cmd 0).host σ₀ σ₀ 1 _ _ .diverged
      simp [world, cmd_bind.2]
    · show Ediv σ₀ σ₀ 1 _ _ .diverged
      exact .inr ⟨rfl, rfl⟩
  exact host_diverged_not_must hq hfa he' hW hm₃

end FVA.Wasi.LaunchExample
