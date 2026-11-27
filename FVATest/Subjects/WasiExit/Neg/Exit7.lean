import FVATest.Subjects.WasiExit.Proof
/-! E1 negative: the exit status is pinned to the run. Claiming status 7 along the same proof path
must not prove — the command calls `proc_exit 0`. -/
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Machine FVA.Wasi FVA.Wasi.LaunchExample
example : ∀ c mem, Launch cmd "_start" [] c mem → ∀ σ₀ : State, σ₀.exited = none →
    SysMust ((world cmd mem).restrict (E cmd mem)) true
      (fun o => ∃ τ s, o = .exited τ s 7) (σ₀, c) := by
  intro c mem hl σ₀ he
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
