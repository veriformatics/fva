# Lessons: `../cnl-ckc` (user pointed an agent at formal verification; read-only survey, HEAD def85431)

Project: clinical guidelines → ACE (controlled English) → Prolog KB; Rust consumer verified in
Verus (`ckc-spec` human-read spec, `ckc-kernel` AI impl + proofs, `--no-cheating`, trust-audit);
Prolog emission certified per document by translation validation (`ckc certify`).
661 commits, 2026-07-18 → 2026-10-19.

| finding | evidence |
|---|---|
| Human-read spec exploded: plan target ≤1.5K lines → 15,188 lines (`rust/ckc-spec/src`, 14 files); kernel 139,860 lines (9.2×) | `.agent/archive/review-implement.md` R-02 "plan target ≤1.5K not met; size = register per user ruling"; spec growth 451 (08-31) → 8,665 (09-21) → 14,393 (10-18) |
| The one "human-read spec audit" was run by an agent reviewer (`rev-spec`) | review-implement.md R-01..R-03 |
| No clinician decisions recorded yet = deliberate: the user starts review once development reaches a stopping point; not evidence about the approach, no FVA action | user statement; `git ls-files` → adjudication.tsv only under `tests/` |
| Pinned verifier unsound: Verus 0.2026.08.30 `compute_only` proves `ensures false` (8/11 upstream false-proof shapes verify); kernel proofs carry 1005 `compute_only` sites; agents filed ~10 more Verus soundness issues (#3144–#3160) | `.agent/deferred.md` rows 7, 9 |
| SMT brittleness: z3 rlimit-count overflow panics, rlimit tuning = proof changes; Kani/CBMC could not finish the engine harness (rc124 at 1200 s) | `.claude/rules/rust.md` `verify` + Kani bullets |
| Verifiability forced a language migration (Prolog consumer → Rust) + translation validation for the part left in Prolog | spec.md Decisions "Consumption→Rust affirmed: no mature Prolog verifier" |
| CNL as the human-readable spec reads as English but drops meaning: relation-structure loss in 209 of 337 CDC documents, condition-scope 96, quantification 68 | `docs/m7-gap-taxonomy.md` |
| Convergent with FVA: escape-hatch audit (`ckc trust-audit` ≈ `fva trust`), byte-pinned trusted surface, version-bound review ledger (≈ review-ledger variant), local review UI (≈ review-page) | README Design; `.claude/rules/rust.md` trust-audit |
