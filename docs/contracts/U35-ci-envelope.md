# U35 contract — the C++ claim's CI envelope (tier: glue; a defect re-checked by every CI trust run)

Purpose: U28g's `fva trust` on CppEH must fit a GitHub-hosted runner (4 CPUs, 16 GB) in default and `--paranoid` mode. CI probe run 43316793091 (`.scratch/lwr/u28g/probe/out/summary.txt`): PASS default 482 s + paranoid 869 s, but the con kernels take the host's thread count: con-leche 8.0 GB, con-ron 8.9 GB, and `fva trust` checks the export three kernels at a time in fixed batches (`FVA/Tool/Trust.lean`: run-set order, `kernels` order) ⇒ paranoid batch 2 = nanoda (1.6 GB) + con-leche + con-ron ≈ 18.5 GB + the `fva` process (2.5 GB): 21 GB when their peaks meet (the probe missed it by timing: max tree RSS 13.5 GB). Consumers: every `fva trust` run (CI trust group, subject shards, acceptance), U28g's CppEH rows.

## Measurements (CppEH's export, 197 MB, on the CI probe's runner)
| kernel | jobs | wall s | user s | max RSS GB |
|---|---|---|---|---|
| con-leche | 4 | 138.7 | 468.5 | 8.04 |
| con-leche | 2 | 184.4 | 337.7 | 4.61 |
| con-leche | 1 | 323.1 | 315.0 | 2.70 |
| con-ron | 4 | 70.7 | 241.0 | 8.92 |
| con-ron | 2 | 100.1 | 186.2 | 5.47 |
| con-ron | 1 | 182.3 | 179.7 | 3.55 |
Jobs 2 = the knee: memory −43 % / −39 % against jobs 4 for +33 % / +42 % wall; jobs 1 halves memory again at +75 % / +82 % wall, which the runner does not need (batch 2 at jobs 2 ≈ 1.6 + 4.6 + 5.5 + 2.5 = 14.2 GB < 16 GB).

## Predicates
- C1 `FVA/Trust/Replay.lean`: con-leche + con-ron run with `--jobs=2` (one named constant, the measurement in its docstring); `Kernel.configId` covers the argument ⇒ their cached canary statuses re-run once; `fva trust` still decides every pinned known-false canary at its default limit (FVA's self package PASS default + `--paranoid`, locally and in the CI trust group); con walls on the runner = the probe's (Measurements); a CI trust step prints its total alone (`scripts/gate` deletes step logs on success: `main`'s rerun 44005516046 shows `trust 594.3 s`, no kernel) ⇒ U35's CI trust step (jobs 2) is recorded beside P′ pins' run 46134704637 (the runner's 4 threads: 837 s; U37's run, same trust content: 992 s = the runner's spread) and stays under the gate's longest job (a subject shard); `trust/canaries/matrix.tsv` regenerated on a dedicated hosted runner at `--canary-limit 120` (a loaded host times out positive perf canaries near the limit: measured on the desktop at load ≈ 25, leanchecker-paranoid too, its invocation unchanged), each con status change recorded and the default run set (V3) re-justified.
- C2 `scripts/subject-matrix`: a subject row's optional 5th field `mem=D/P` (GiB, positive integers) replaces the mode weights `wmem` (default 6, paranoid 9) for that row's default / paranoid run; CPU weights unchanged; a run whose weight exceeds the whole budget still runs, alone (never skipped or starved); a malformed field → rc 2 naming the row; `FVA_SUBJECT_MEM=<GiB>` overrides the measured budget (MemAvailable, cgroup-capped) for tests. `scripts/test-subject-matrix` cases: two weighted rows whose sum exceeds the budget never overlap (stub timestamps) while two light rows do; an over-budget row completes; `mem=0/9`, `mem=x`, `mem=6` → rc 2.
- C3 `scripts/gate` + `gate.yml`: CI group `accept` = `build accept` (`scripts/test-accept`), removed from `lean`; `gate.yml`'s matrix lists `accept`; ci-groups' clean case over the real `gate.yml` passes.
- C4 downstream (U28g): CppEH's rows carry `mem=10/15` (default: fva 2.5 + leanchecker 2.3 + con-leche 4.6 + slack; paranoid: batch 2 ≈ 14.2 + slack); U28g's CI run = the envelope's acceptance (default + paranoid PASS; walls + peak RSS from a hosted probe of the same tree, `/usr/bin/time` + a process sampler per mode, as the probe's: a CI step prints its total alone).

## Residual
- R1 the batch order is `kernels` order: a reorder can put both con kernels beside a heavier third; C1's bound keeps any triple of today's kernels ≤ 14.2 GB + the `fva` process on CppEH's export.
- R2 weights are per row, measured on one artifact: a larger subject needs its own measured `mem=`.
