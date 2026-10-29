import FVA.Proof.Lib

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Proofs.Execution

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

theorem walk_to_empty_unique {H : HostSem} {k : Nat} {c d e : Config}
    (hw : walk k c = some d) (hd : d.instrs = [])
    (he : e.instrs = []) (hs : Steps H c e) : e = d := by
  induction k generalizing c with
  | zero =>
    have hcd : c = d := Option.some.inj hw
    subst c
    cases d with
    | mk s f es =>
      dsimp at hd
      subst es
      exact steps_nil hs
  | succ k ih =>
    simp only [walk] at hw
    cases hu : uniqueStep c <;> simp only [hu, Bool.cond_false, Bool.cond_true] at hw
    · contradiction
    cases hp : step c <;> simp only [hp, Option.bind_none, Option.bind_some] at hw
    · contradiction
    rename_i c'
    rcases hs.cases_head with hce | ⟨mid, hstep, hrest⟩
    · have hcempty : c.instrs = [] := by simpa [hce] using he
      have hstep := step_sound (H := H) hp
      cases c with
      | mk s f es =>
        dsimp at hcempty
        subst es
        exact False.elim (no_step_nil hstep)
    · have hm : mid = c' := step_complete hstep hp hu
      subst mid
      exact ih hw hrest

end Proofs.Execution
