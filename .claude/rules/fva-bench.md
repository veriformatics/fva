---
paths:
  - "prototype/bench/**"
  - "bench/**"
---

# Agent benchmark law

- Rubric first: `rubric.md` (or a dated addendum) is committed before any run it grades; scoring follows it as written, a deviation = a new addendum + a note in `results.md`.
- Arms run as fresh `codex exec` sessions in dirs outside this repo (own `git init`), because teammates inherit this repo's `CLAUDE.md` + `spec.md` (FVA's whole approach) and a copy of the repo leaks the rubric + planted-bug commit messages; the fva arm gets a history-free copy of the FVA package (v1: `git archive` of `prototype/fva`; v2: `fva init`'s vendored package, prebuilt, + the fetched canaries, assembled by `bench/tasks/prepare` from the bench tag's frozen worktree). `codex exec` needs `< /dev/null`, else it blocks on stdin.
- Every agent claim is rechecked by MAIN: clean build, axiom audit, `leanexport` → `lake check --from-export` kernel replay (outside the agent sandbox; nested `bwrap` fails inside it, D19); judged metrics (M3/M4/M6) go to a fresh `reviewer` per arm, calibrated on the earlier `verdicts.md`.
- `inject.py` (M8) counts a catch only when the arm's own check exits nonzero or names the cheat; confirm each catch's cause in its log, since a syntax error from the injection would also exit nonzero.
- Graded batch = `bench/harness/run-batch TASK SEED ARM…` (one task, every arm × n = 5, seeded interleaved order recorded under `~/.cache/fva-bench/batches/`, one run per CPU 2–7; inputs prepared once per arm; fva arm = `FVA_BENCH_FVA_BIN`/`FVA_BENCH_FVA_BUILD` of the bench tag's frozen worktree). Before each batch the user pauses their heavy jobs on the host and MAIN runs no heavy job there; after each, `bench/tools/codex-quota` → `results.md`.
