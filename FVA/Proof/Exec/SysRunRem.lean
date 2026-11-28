import FVA.Impl.Exec.SysRunRem

/-! `fva run`'s step-counting run (U29b2) stops where `sysRun` does, and the fuel it reports
left = the fuel it did not spend: the driver's states are `sysRun`'s (so `machineRun_sysMust` and
the host theorems speak about them) and `--fuel N` counts steps exactly. -/

namespace FVA.Wasm.Exec.Machine

/-- `sysRunRem` = `sysRun` plus the fuel left. -/
theorem sysRunRem_eq {St : Type} (exited : St → Option Nat)
    (X : St → Nat → MStore → List Val → Option (St × MStore × MHostOut)) :
    ∀ (n : Nat) (x : St × MState),
      ((sysRunRem exited X n x).1, (sysRunRem exited X n x).2.1, (sysRunRem exited X n x).2.2.1) =
        sysRun exited X n x
  | 0, (σ, m) => rfl
  | n + 1, (σ, m) => by
    unfold sysRunRem sysRun
    cases he : exited σ with
    | some _ => rfl
    | none =>
      simp only
      cases hh : m.hostCall with
      | some p =>
        obtain ⟨id, k, rest⟩ := p
        simp only
        cases hx : X σ id m.store (m.stack.take k).reverse with
        | some q =>
          obtain ⟨τ, ms, r⟩ := q
          exact sysRunRem_eq exited X n _
        | none => rfl
      | none =>
        simp only
        cases hu : (m.uniq true || m.admin)
        · rfl
        · simp only [Bool.cond_true]
          cases hs : m.step with
          | some m' => exact sysRunRem_eq exited X n _
          | none => rfl

/-- The fuel `sysRunRem` leaves = the fuel it did not spend: `sysRun` given exactly the spent
fuel reaches the same state, exhausted. -/
theorem sysRunRem_spent {St : Type} (exited : St → Option Nat)
    (X : St → Nat → MStore → List Val → Option (St × MStore × MHostOut)) :
    ∀ (n : Nat) (x : St × MState), (sysRunRem exited X n x).2.2.2 ≤ n ∧
      sysRun exited X (n - (sysRunRem exited X n x).2.2.2) x =
        ((sysRunRem exited X n x).1, (sysRunRem exited X n x).2.1, true)
  | 0, (σ, m) => ⟨Nat.le_refl 0, rfl⟩
  | n + 1, (σ, m) => by
    have stop : n + 1 ≤ n + 1 ∧ sysRun exited X (n + 1 - (n + 1)) (σ, m) = (σ, m, true) :=
      ⟨Nat.le_refl _, by rw [Nat.sub_self]; rfl⟩
    unfold sysRunRem
    cases he : exited σ with
    | some _ => exact stop
    | none =>
      simp only
      cases hh : m.hostCall with
      | some p =>
        obtain ⟨id, k, rest⟩ := p
        simp only
        cases hx : X σ id m.store (m.stack.take k).reverse with
        | some q =>
          obtain ⟨τ, ms, r⟩ := q
          simp only
          obtain ⟨hle, heq⟩ := sysRunRem_spent exited X n (τ, m.hostResume ms r.out rest k)
          refine ⟨Nat.le_succ_of_le hle, ?_⟩
          rw [Nat.succ_sub hle]
          simp only [sysRun, he, hh, hx]
          exact heq
        | none => exact stop
      | none =>
        simp only
        cases hu : (m.uniq true || m.admin)
        · exact stop
        · simp only [Bool.cond_true]
          cases hs : m.step with
          | some m' =>
            simp only
            obtain ⟨hle, heq⟩ := sysRunRem_spent exited X n (σ, m')
            refine ⟨Nat.le_succ_of_le hle, ?_⟩
            rw [Nat.succ_sub hle]
            simp only [sysRun, he, hh, hu, hs, Bool.cond_true]
            exact heq
          | none => exact stop

end FVA.Wasm.Exec.Machine
