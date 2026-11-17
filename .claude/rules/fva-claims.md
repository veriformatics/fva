---
paths:
  - "FVA/Self/Spec.lean"
  - "FVA/Spec/Claims.lean"
  - "FVA/Spec/CAbi.lean"
  - "FVA/Spec/Cert.lean"
  - "FVA/Spec/Rel/*.lean"
  - "FVA/Tool/Call.lean"
  - "FVA/Tool/Certify.lean"
  - "scripts/make-certs"
  - "FVATest/Subjects/**/Spec.lean"
  - "FVATest/Subjects/**/Call.lean"
  - "FVATest/Subjects/EdgerCpm/Contract.lean"
  - "FVATest/Subjects/Lz4/Any.lean"
  - "FVATest/Subjects/Lz4/Format.lean"
  - "FVATest/Subjects/Tmm/Exact.lean"
  - "FVATest/Subjects/Tmm/Rel.lean"
  - "FVATest/Certs/**/Spec.lean"
  - "FVATest/Certs/Custom/Rel.lean"
  - "FVATest/Examples/**/Spec.lean"
  - "FVATest/Examples/**/requirements.md"
---
# Claim review

- Each new or edited claim, vocabulary definition or claim template (`fva certify`, `fva call`; a certificate claim = its `scripts/make-certs` line: relation, input + output) → one row per item of `AGENT.md` item 2's attack list in the unit's commit body; a row = `pass` | `n/a` + why | a finding with its witness (a kernel-checked counterexample or instance, `file:line`), never a paraphrase. Why: the kernel checks proofs + `fva trust` checks axioms, layout + links; nothing checks that a statement means its requirement (`fva explain` = advisory), so a vacuous premise, a reversed `→` or a stand-in conclusion passes every gate (TauCetiReview `rubrics/correctness.md`).
- Exempt = fixtures false or mismatched on purpose: cheats (`FVATest/Cheats/**`), false certificates (`FVATest/Certs/Neg/**`), `fva explain`'s test beds (`FVATest/Examples/{Planted,Mislabeled,Relational}`).
- `paths:` = the claim modules, their sources (claim templates, `scripts/make-certs`) + the vocabulary they import: subject, example + certificate modules, and FVA's claim + certificate vocabulary (`Claims`, `CAbi`, `Cert`, `Rel/*`; the other base specs = reviewed once under their own contracts) → a new one joins it.
