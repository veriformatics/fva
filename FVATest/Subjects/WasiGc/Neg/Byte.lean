import FVATest.Subjects.WasiGc.Proof
/-! Negative: the output is pinned to the run. Claiming one wrong digit (`9 17` for `8 17`) along
the same proof path must not prove: the kernel evaluates the run and its stdout differs. -/
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Machine FVA.Wasi Subjects.WasiGc
example : ∀ c mem, Launch Lifted.module "_start" [] c mem →
    SysMust ((world Lifted.module mem).restrict (E Lifted.module mem)) true
      (fun o => ∃ τ s, o = .exited τ s 0 ∧ τ.stdout = ascii "9 17\n") (start, c) := by
  intro c mem hl
  have eta : ∀ p : State × MState × Bool, p = (p.1, p.2.1, p.2.2) := fun _ => rfl
  have hex : ((world Lifted.module 0).restrict (E Lifted.module 0)).exited = State.exited := rfl
  have he : ((world Lifted.module 0).restrict (E Lifted.module 0)).exited run.1 = some 0 := by
    rw [hex]; exact run_exits
  have hout : run.1.stdout = ascii "9 17\n" := by decide +kernel
  exact launch_sysMust inst_eq start_export memory_export (eta run)
    (sysMust_exited he ⟨run.1, _, rfl, hout⟩) c mem hl
