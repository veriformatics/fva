---
paths:
  - "prototype/bench/**"
  - "bench/**"
---

# Agent benchmark law

- Rubric first: `rubric.md` (or a dated addendum) is committed before any run it grades; scoring follows it as written, a deviation = a new addendum + a note in `results.md`.
- Arms run as fresh `codex exec` sessions in dirs outside this repo (own `git init`), because teammates inherit this repo's `CLAUDE.md` + `spec.md` (FVA's whole approach) and a copy of the repo leaks the rubric + planted-bug commit messages; the fva arm gets a history-free copy of the FVA package (v1: `git archive` of `prototype/fva`; v2: `fva init`'s vendored package, prebuilt, + the fetched canaries, assembled by `bench/tasks/prepare` from the bench tag's frozen worktree). `codex exec` needs `< /dev/null`, else it blocks on stdin.
- `bench/harness/run-session` jails every run (bubblewrap; visible = system, own run dir, arm tools, package store, `PATH` entries under `$HOME`), since Codex's workspace-write sandbox limits writes alone and agents read ancestor `AGENTS.md` files; a graded run's `result.json` carries `jail.visible` + a clean `harness_commit`. `bench/tests/check-prep` (by hand, mock Codex) asserts the jail.
- Every agent claim is rechecked by MAIN: clean build, axiom audit, `leanexport` → `lake check --from-export` kernel replay (outside the agent sandbox; nested `bwrap` fails inside it, D19); judged metrics (M3/M4/M6) go to a fresh `reviewer` per arm, calibrated on the earlier `verdicts.md`.
- `bench/grade/inject` (Lean arms) + `bench/grade/inject-tool` (Frama-C arms) (M8) count a catch only when the arm's own check exits nonzero or its output names the cheat by a cheat-specific token (`sorryAx`, `fvaCheatAx`, `fvaCheatOneEqTwo`, a byte/hash mismatch; generic words such as `axioms` or `kernel` appear in clean output too); confirm each catch's cause in its log, since a syntax error from the injection would also exit nonzero, and run the clean baseline (`C0`) of every documented check: a check red on a clean copy credits catches by name alone.
- Graded batch = `bench/harness/run-batch TASK SEED ARM…` (one task, every arm × n = 5, seeded interleaved order recorded under `~/.cache/fva-bench/batches/`, one run per CPU 2–7; inputs prepared once per arm; fva arm = `FVA_BENCH_FVA_BIN`/`FVA_BENCH_FVA_BUILD` of the bench tag's frozen worktree). Before each batch the user pauses their heavy jobs on the host and MAIN runs no heavy job there; after each, `bench/tools/codex-quota` → `results.md`.
