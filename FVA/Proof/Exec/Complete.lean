import FVA.Proof.Exec.Det

/-!
# Reference-run completeness and total-correctness adequacy

`uniqueStep` excludes semantic choice points but permits malformed configurations where `seq`
is stuck despite a semantic step. Completeness therefore also requires operational non-stuckness
at reachable nonterminal configurations. Final configurations need neither hypothesis.
-/

namespace FVA.Wasm.Exec.Ref

open FVA.Wasm FVA.Wasm.Exec

theorem seq_of_final {c : Config} {o : Outcome} (hf : Final c o) :
    seq c.store c.frame [] c.instrs = .final ∨
      ∃ a, seq c.store c.frame [] c.instrs = .thrown a := by
  cases o with
  | returned s vs => rw [hf.2]; exact .inl (seq_values _ _ _ _)
  | trapped s => rw [hf.2]; exact .inl rfl
  | thrown s a => rw [hf.2]; exact .inr ⟨a, rfl⟩

theorem seq_of_step {H : HostSem} {c c' : Config} (hs : Step H c c')
    (hu : uniqueStep false c = true) (hp : seq c.store c.frame [] c.instrs ≠ .stuck) :
    seq c.store c.frame [] c.instrs = .step c'.store c'.frame c'.instrs := by
  have hc := seq_complete hs [] [] (by simpa only [uniqueStep, List.append_nil] using hu)
  simp only [List.append_nil, List.reverse_nil, vals, List.map_nil, List.nil_append] at hc
  exact hc.resolve_right hp

/-- Every finite semantic execution in the deterministic executable domain has a fuel witness.
Only states with a successor need uniqueness and non-stuckness; terminal traps are included. -/
theorem run_complete {H : HostSem} {c c' : Config} {o : Outcome}
    (hu : ∀ d e, Steps H c d → Step H d e → uniqueStep false d = true)
    (hp : ∀ d e, Steps H c d → Step H d e →
      seq d.store d.frame [] d.instrs ≠ .stuck)
    (hs : Steps H c c') (hf : Final c' o) : ∃ n, run n c = some c' := by
  revert hu hp
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hu hp
    rcases seq_of_final hf with h | ⟨a, h⟩ <;> exact ⟨1, by simp only [run, h]⟩
  | @head c d hstep hrest ih =>
    intro hu hp
    obtain ⟨n, hn⟩ := ih
      (fun e f he hs => hu e f (.head hstep he) hs)
      (fun e f he hs => hp e f (.head hstep he) hs)
    have he := seq_of_step hstep (hu c d .refl hstep) (hp c d .refl hstep)
    exact ⟨n + 1, by simpa only [run, he] using hn⟩

/-- A total-correctness proof contains a finite successful execution, even with choice points. -/
theorem _root_.FVA.Wasm.Exec.Must.may {H : HostSem} {Q : Outcome → Prop} {c : Config}
    (hm : Must H Q c) : May H Q c := by
  induction hm with
  | done hf hq => exact ⟨_, _, .refl, hf, hq⟩
  | next hex hnext ih =>
    obtain ⟨d, hs⟩ := hex
    obtain ⟨e, o, he, hf, hq⟩ := ih d hs
    exact ⟨e, o, .head hs he, hf, hq⟩

/-- On a unique-step domain, a terminating reference run proves total correctness. -/
theorem run_must {H : HostSem} {Q : Outcome → Prop} {n : Nat} {c c' : Config}
    (hu : ∀ d e, Steps H c d → Step H d e → uniqueStep false d = true)
    (hr : run n c = some c') (hq : ∀ o, Final c' o → Q o) : Must H Q c := by
  induction n generalizing c with
  | zero => simp only [run, reduceCtorEq] at hr
  | succ n ih =>
    cases hs : seq c.store c.frame [] c.instrs with
    | step s f es =>
      have hstep : step c = some ⟨s, f, es⟩ := by simp only [step, hs]
      have hsem : Step H c ⟨s, f, es⟩ := step_sound hstep
      refine must_of_step hstep (hu _ _ .refl hsem) (ih ?_ ?_)
      · intro d e hd he
        exact hu d e (.head hsem hd) he
      · simpa only [run, hs] using hr
    | final | thrown _ =>
      have he : c = c' := Option.some.inj (by simpa only [run, hs] using hr)
      subst c'
      obtain ⟨_, hf⟩ := (run_sound (H := H) hr).2
      exact Must.done hf (hq _ hf)
    | _ => simp only [run, hs, reduceCtorEq] at hr

/-- Total correctness equals a successful reference run on the deterministic executable domain. -/
theorem must_iff_run {H : HostSem} {Q : Outcome → Prop} {c : Config}
    (hu : ∀ d e, Steps H c d → Step H d e → uniqueStep false d = true)
    (hp : ∀ d e, Steps H c d → Step H d e →
      seq d.store d.frame [] d.instrs ≠ .stuck) :
    Must H Q c ↔ ∃ n c', run n c = some c' ∧ ∀ o, Final c' o → Q o := by
  constructor
  · intro hm
    obtain ⟨d, o, hs, hf, _⟩ := hm.may
    obtain ⟨n, hn⟩ := run_complete hu hp hs hf
    exact ⟨n, d, hn, fun o ho => hm.outcome hs ho⟩
  · rintro ⟨n, d, hr, hq⟩
    exact run_must hu hr hq

end FVA.Wasm.Exec.Ref
