import FVA.Impl.Exec.Machine

/-!
# `sysRun` with the fuel it left (U29b2)

`fva run --fuel N` counts machine steps exactly: its driver runs `sysRun` in segments and needs
the steps each one spent (`FVA.Proof.Exec.SysRunRem`: `sysRunRem_eq`, `sysRunRem_spent`).
-/

namespace FVA.Wasm.Exec.Machine

/-- `sysRun`, also returning the fuel left when it stopped. -/
def sysRunRem {St : Type} (exited : St → Option Nat)
    (X : St → Nat → MStore → List Val → Option (St × MStore × MHostOut)) :
    Nat → St × MState → St × MState × Bool × Nat
  | 0, (σ, m) => (σ, m, true, 0)
  | n + 1, (σ, m) =>
    match exited σ with
    | some _ => (σ, m, false, n + 1)
    | none => match m.hostCall with
      | some (id, k, rest) => match X σ id m.store (m.stack.take k).reverse with
        | some (τ, ms, r) => sysRunRem exited X n (τ, m.hostResume ms r.out rest k)
        | none => (σ, m, false, n + 1)
      | none => bif m.uniq true || m.admin then
          match m.step with
          | some m' => sysRunRem exited X n (σ, m')
          | none => (σ, m, false, n + 1)
        else (σ, m, false, n + 1)

end FVA.Wasm.Exec.Machine
