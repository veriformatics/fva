import FVATest.Subjects.WasiExit.Lifted
import FVA.Spec.Wasi.World

/-!
# A minimal WASI command exits with status 0 (claim; contract U29b T4)

`exit.wasm` (`wasm-tools parse exit.wat`) imports `fd_write` and `proc_exit`, exports its memory
and `_start`, which calls `proc_exit 0`. The claim is a process claim under the reviewed WASI model
(`world`) restricted to the environment `E` (in-profile calls return), with fitting growth.
-/

namespace Subjects.WasiExit

open FVA.Wasm FVA.Wasm.Exec FVA.Wasi

/-- The command launches at `_start`, and each launch, from every live world, exits with
status 0. -/
@[fva_claim] def exitsZero : Prop :=
  (∃ c mem, Launch Lifted.module "_start" [] c mem) ∧
    ∀ c mem, Launch Lifted.module "_start" [] c mem → ∀ σ₀ : State, σ₀.exited = none →
      SysMust ((world Lifted.module mem).restrict (E Lifted.module mem)) true
        (fun o => ∃ τ s, o = .exited τ s 0) (σ₀, c)

end Subjects.WasiExit
