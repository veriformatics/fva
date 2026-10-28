import Proofs.MemorySpec
import FVA.Proof.Lib

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref
set_option maxHeartbeats 0

/-- A finite certificate checks every configuration along a unique execution.
Stuck states, choice points, pending traps, and exhausted fuel are rejected. -/
def checkTrace (src dst size capacity : Nat) : Nat → Config → Bool
  | 0, _ => false
  | n + 1, c =>
    bif accessesAllowed src dst size capacity c && uniqueStep c then
      match seq c.store c.frame [] c.instrs with
      | .step s f es => checkTrace src dst size capacity n ⟨s, f, es⟩
      | .final => true
      | _ => false
    else false

theorem checkTrace_sound {src dst size capacity fuel : Nat} {H : HostSem} {c : Config}
    (h : checkTrace src dst size capacity fuel c = true) :
    Throughout H (fun c => accessesAllowed src dst size capacity c = true) c := by
  induction fuel generalizing c with
  | zero => simp [checkTrace] at h
  | succ n ih =>
    cases ha : accessesAllowed src dst size capacity c <;>
      simp only [checkTrace, ha, Bool.false_and, Bool.true_and, Bool.false_eq_true,
        Bool.cond_false] at h
    cases hu : uniqueStep c <;>
      simp only [hu, Bool.cond_false, Bool.cond_true, Bool.false_eq_true] at h
    intro target hsteps
    cases hsteps.cases_head with
    | inl he => simpa only [← he] using ha
    | inr hs =>
      obtain ⟨next, hs, hrest⟩ := hs
      have hc := seq_complete hs [] [] (by simpa [uniqueStep] using hu)
      cases he : seq c.store c.frame [] c.instrs with
      | step s f es =>
        have hn : Step H c ⟨s, f, es⟩ := step_sound (by simp only [step, he])
        have hn' : next = ⟨s, f, es⟩ := step_complete hs (by simp only [step, he]) hu
        subst next
        apply ih (by simpa only [he] using h) target hrest
      | final => simp only [List.append_nil, he, reduceCtorEq, or_self] at hc
      | br k vs => simp only [he, Bool.false_eq_true] at h
      | ret vs => simp only [he, Bool.false_eq_true] at h
      | stuck => simp only [he, Bool.false_eq_true] at h
end Proofs
