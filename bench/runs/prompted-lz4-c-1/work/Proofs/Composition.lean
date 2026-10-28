import Proofs.Wasm
namespace Wasm

def advance (fs : List Func) : Nat → State → Option State
  | 0, s => some s
  | n+1, s => do
    let .next t ← step fs s | none
    advance fs n t

theorem run_of_advance (fs : List Func) (n fuel : Nat) (s t : State) (out : Nat × State)
    (h : advance fs n s = some t) (tail : run fs fuel t = some out) :
    run fs (n+fuel) s = some out := by
  induction n generalizing s with
  | zero =>
    have heq : s = t := Option.some.inj h
    subst s
    simpa using tail
  | succ n ih =>
    cases hs : step fs s with
    | none => simp [advance, hs] at h
    | some st =>
      cases st with
      | done r u => simp [advance, hs] at h
      | next u =>
        have h' : advance fs n u = some t := by simpa [advance, hs] using h
        have hrun := ih u h'
        simpa [Nat.succ_add, run, hs] using hrun
end Wasm
