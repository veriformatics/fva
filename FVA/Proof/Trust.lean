import FVA.Trust.Verdict

/-!
# The verdict function decides the verdict spec

One emptiness lemma per rule, then `issues_nil_iff` (no issue ⇔ `Pass`) and `verdict_pass_iff`.
-/

namespace FVA.Trust

theorem Status.bad_iff (s : Status) : s.bad = true ↔ s.Bad := by
  cases s <;> simp [Status.bad, Status.Bad]

theorem Link.ok_iff (l : Link) : l.ok = true ↔
    l.present = true ∧ l.bytesMatch = true ∧ l.lenMatch = true ∧
      (l.kind = .wasm → l.decodeEq = true) ∧ l.regenerates = true := by
  cases h : l.kind <;> simp [Link.ok, Bool.and_eq_true, and_assoc, h]

theorem ruleBuild_nil (r : Report) : ruleBuild r = [] ↔ r.built = true := by
  unfold ruleBuild; split <;> simp_all

theorem ruleClaims_nil (r : Report) : ruleClaims r = [] ↔ r.claims ≠ [] := by
  unfold ruleClaims; split <;> simp_all [List.isEmpty_iff]

theorem ruleUnproven_nil (r : Report) : ruleUnproven r = [] ↔ ∀ c ∈ r.claims, c.proofs ≠ [] := by
  simp only [ruleUnproven, List.flatMap_eq_nil_iff]
  refine forall₂_congr fun c _ => ?_
  split <;> simp_all [List.isEmpty_iff]

theorem ruleAxiom_nil (r : Report) : ruleAxiom r = [] ↔
    ∀ c ∈ r.claims, ∀ p ∈ c.proofs, ∀ a ∈ p.axioms, a ∈ standardAxioms := by
  simp only [ruleAxiom, List.flatMap_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff,
    Bool.not_eq_true', List.contains_iff_mem, Bool.not_eq_false]

theorem ruleVacuous_nil (r : Report) : ruleVacuous r = [] ↔ ∀ c ∈ r.claims, c.subjects ≠ [] := by
  simp only [ruleVacuous, List.flatMap_eq_nil_iff]
  refine forall₂_congr fun c _ => ?_
  split <;> simp_all [List.isEmpty_iff]

theorem ruleLayout_nil (r : Report) :
    ruleLayout r = [] ↔ ∀ c ∈ r.claims, c.provenInSpec = false := by
  simp only [ruleLayout, List.flatMap_eq_nil_iff]
  refine forall₂_congr fun c _ => ?_
  split <;> simp_all

theorem ruleOverride_nil (r : Report) : ruleOverride r = [] ↔ r.flags = [] := by
  simp [ruleOverride]

theorem ruleSyntax_nil (r : Report) : ruleSyntax r = [] ↔
    (∀ m ∈ r.reviewModules, m.syntaxExts = []) ∧ r.subjectSyntax = [] := by
  simp only [ruleSyntax, List.append_eq_nil_iff, List.flatMap_eq_nil_iff]
  refine and_congr (forall₂_congr fun m _ => ?_) ?_
  · split <;> simp_all [List.isEmpty_iff]
  · split <;> simp_all [List.isEmpty_iff]

theorem rulePrelude_nil (r : Report) : rulePrelude r = [] ↔ r.prelude = [] := by
  simp [rulePrelude]

theorem ruleLink_nil (r : Report) : ruleLink r = [] ↔ (r.needsLink = true → r.links ≠ []) ∧
    ∀ l ∈ r.links, l.present = true ∧ l.bytesMatch = true ∧ l.lenMatch = true ∧
      (l.kind = .wasm → l.decodeEq = true) ∧ l.regenerates = true := by
  simp only [ruleLink, List.append_eq_nil_iff, List.flatMap_eq_nil_iff]
  refine and_congr ?_ (forall₂_congr fun l _ => ?_)
  · split <;> simp_all [List.isEmpty_iff]
  · rw [← Link.ok_iff]; split <;> simp_all

theorem ruleReplay_nil (r : Report) : ruleReplay r = [] ↔ r.exportOk = true ∧
    (∀ k ∈ r.replay, ¬ k.status.Bad) ∧ ∃ k ∈ r.replay, k.status = .accept ∧ k.lineage ≠ "lean" := by
  simp only [ruleReplay, List.flatten_eq_nil_iff, List.forall_mem_cons, List.mem_nil_iff,
    false_implies, implies_true, and_true, List.flatMap_eq_nil_iff]
  refine and_congr ?_ (and_congr (forall₂_congr fun k _ => ?_) ?_)
  · split <;> simp_all
  · rw [← Status.bad_iff]; split <;> simp_all
  · split <;> simp_all [List.any_eq_true]

theorem canaryCovered_iff (cs : List CanaryRun) (c : CanaryRun) :
    canaryCovered cs c = true ↔
      c.knownAccept = true ∧ ∃ d ∈ cs, d.canary = c.canary ∧ d.status = .reject := by
  simp [canaryCovered, List.any_eq_true]

theorem untested_nil (r : Report) (k : KernelRun) : untested r k = [] ↔
    ∀ n ∈ r.canarySet, ∃ c ∈ r.canaries, c.kernel = k.kernel ∧ c.canary = n ∧
      c.status ≠ .timeout := by
  simp [untested, List.filter_eq_nil_iff]

theorem ruleChecker_nil (r : Report) : ruleChecker r = [] ↔ r.canarySet ≠ [] ∧
    (∀ k ∈ r.replay, ∀ n ∈ r.canarySet,
      ∃ c ∈ r.canaries, c.kernel = k.kernel ∧ c.canary = n ∧ c.status ≠ .timeout) ∧
    ∀ c ∈ r.canaries, c.status = .accept → c.knownAccept = true ∧
      ∃ d ∈ r.canaries, d.canary = c.canary ∧ d.status = .reject := by
  simp only [ruleChecker, List.append_eq_nil_iff, List.flatMap_eq_nil_iff, and_assoc]
  refine and_congr ?_ (and_congr (forall₂_congr fun k _ => ?_) (forall₂_congr fun c _ => ?_))
  · split <;> simp_all [List.isEmpty_iff]
  · rw [← untested_nil]; split <;> simp_all
  rw [← canaryCovered_iff]
  by_cases hacc : c.status = .accept <;> by_cases hcov : canaryCovered r.canaries c = true <;>
    simp [hacc, hcov]

theorem ruleSources_nil (r : Report) :
    ruleSources r = [] ↔ ∀ m ∈ r.reviewModules, m.found = true := by
  simp only [ruleSources, List.flatMap_eq_nil_iff]
  refine forall₂_congr fun m _ => ?_
  split <;> simp_all

theorem ruleBudget_nil (r : Report) :
    ruleBudget r = [] ↔ ∀ b, r.budget = some b → r.surfaceLines ≤ b := by
  unfold ruleBudget
  split
  · rename_i b hb
    simp only [hb, Option.some.injEq, forall_eq']
    split <;> simp_all
  · rename_i hb
    simp [hb]

theorem ruleSurface_nil (r : Report) : ruleSurface r = [] ↔
    (∀ m ∈ r.reviewModules, m.found = true) ∧ ∀ b, r.budget = some b → r.surfaceLines ≤ b := by
  rw [ruleSurface, List.append_eq_nil_iff, ruleSources_nil, ruleBudget_nil]

theorem issues_nil_iff (r : Report) : issues r = [] ↔ Pass r := by
  simp only [issues, List.flatten_eq_nil_iff, List.forall_mem_cons, List.mem_nil_iff,
    false_implies, implies_true, and_true, ruleBuild_nil, ruleClaims_nil, ruleUnproven_nil,
    ruleAxiom_nil, ruleVacuous_nil, ruleLayout_nil, ruleOverride_nil, ruleSyntax_nil,
    rulePrelude_nil, ruleLink_nil, ruleReplay_nil, ruleChecker_nil, ruleSurface_nil]
  constructor
  · rintro ⟨hb, hc, hu, ha, hv, hl, hf, hs, hp, hk, hr, hch, hsu⟩
    exact ⟨hb, hc, hu, ha, hv, hl, hf, hs, hp, hk, hr, hch, hsu⟩
  · rintro ⟨hb, hc, hu, ha, hv, hl, hf, hs, hp, hk, hr, hch, hsu⟩
    exact ⟨hb, hc, hu, ha, hv, hl, hf, hs, hp, hk, hr, hch, hsu⟩

theorem verdict_pass_iff (r : Report) : verdict r = .pass ↔ Pass r := by
  rw [← issues_nil_iff]
  unfold verdict
  cases issues r <;> simp

end FVA.Trust
