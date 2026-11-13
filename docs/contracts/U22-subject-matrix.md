# U22 contract — every subject's `fva trust` in default and `--paranoid` mode (tier kernel)

Tier: kernel (consultant-6 V4: no downstream check detects an omitted or overwritten mode). User ruling (`.agent/spec.md` Decisions, U19 entry): the full gate runs every subject's `fva trust` in both modes; a paranoid PASS ⇏ a default PASS (`FVA/Spec/Trust.lean` `Pass.replay`: a con-leche decline passes when nanoda or con-ron accepts), so neither mode stands in for the other.

## Interface
- `scripts/subject-matrix` (new; bash): reads a subjects table on stdin, one subject per line = `root spec subject surface` (`subject` = `-` for a certificate subject), runs `"$FVA" trust . --spec-module spec --root-module root [--subject subject] [--paranoid]` for every (subject, mode) of the matrix N subjects × {default, paranoid}, prints one line per run `subject-matrix: <root> <mode> <seconds> s`, and exits 0 iff every run passed with the pinned surface. `FVA` (env) = the fva binary (default `.lake/build/bin/fva`); `FVA_SUBJECT_JOBS` (env) caps concurrency.
- `scripts/test-subjects` keeps its other duties (corpus fetch, edgeR lift, root builds, `Neg/*` builds), calls `subject-matrix` with its subjects table and keeps its rc classes: matrix 2 → exit 2 at once, 3 → exit 3 after the `Neg/*` checks, 1 → a failure.

## Verdict rules (fail closed)
- Each run writes its own result: log, rc and seconds keyed by (root, mode); a later run never overwrites another's result.
- A result = the rc the runner's per-run wrapper records after `fva` exits (any rc, signals included). After all runs: exactly 2N results exist, one per (root, mode); a run with no recorded rc (its wrapper died, or it was never scheduled) → FAIL `missing <root> <mode>`; an `fva` that exits non-zero without output is a failed run (`trust rc <rc>`), not a missing one. A root listed twice in the table → setup error (rc 2).
- A run whose `fva` died by a signal (rc ≥ 128) → CRASH (`<root> <mode> crashed, rc <rc>`); any other rc ≠ 0 → FAIL (`<root> <mode> trust rc <rc>` + the log's verdict lines); a run whose log lacks `Read these: <surface> code lines` → FAIL (`<root> <mode> surface ≠ pinned <surface>`). Both modes check the pin.
- Exit (gate rc law, `.claude/rules/fva-gate.md`) 2 on setup errors, else 3 on any CRASH, else 1 on any FAIL (a missing result included), else 0; setup errors = an empty table (2N = 0 never passes), a row with ≠ 4 fields or a non-numeric surface, a root listed twice, the fva binary missing.

## Scheduling (equal strength; affects time only)
- Budget = CPUs from `nproc` (affinity-aware) and memory = min(`MemAvailable`, cgroup `memory.max` − `memory.current` where a limit exists).
- Weights: default run = 2 CPU + 6 GiB (its 2 kernels side by side, ≈ 2.8 GiB peak each on the decoder export); paranoid run = 6 CPU + 9 GiB (3 kernels at a time). A job starts when its weight fits the remaining budget; with nothing running, the next job always starts (progress on small hosts). Canary runs are cached per kernel + canary, and `scripts/test-trust` usually warms that cache before this step; a cold run (a standalone call, a test-trust failure, an uncached timeout: `FVA/Trust/Canary.lean`) fans out up to 4 canary jobs beyond these weights — time only, never a verdict.

## Acceptance (planted, in `scripts/test-checks`, stub `FVA` = a script returning a configured rc + log per (root, mode))
- all runs pass with pinned surfaces → rc 0, 2N `subject-matrix:` lines;
- one subject's paranoid run fails (rc 1), its default run passes → rc 1 naming `<root> paranoid`;
- one subject's default run fails, its paranoid run passes → rc 1 naming `<root> default`;
- one run's wrapper dies before recording its rc (the stub sends SIGKILL to its parent process) → rc 1 naming it missing; one run's stub exits 139 with no output → rc 3 naming `crashed, rc 139`; one run's stub exits 1 → rc 1 naming `trust rc 1`;
- a paranoid run whose surface line differs → rc 1 naming `<root> paranoid surface`; the same for a default run; a run whose log has no surface line at all → rc 1 naming the surface;
- an empty table, a 3-field row, a non-numeric surface, a duplicate root → rc 2 each;
- `FVA_SUBJECT_JOBS=1` (every run alone) → rc 0 with all 2N results (scheduling completeness);
- each case asserts the exact rc and the named (root, mode) diagnostic (not any nonzero rc);
- a neutered matrix (forced `exit 0`) must make `test-checks` fail (U1 law).
- Real runs: the full gate (pool) with every current subject in both modes, per-run seconds printed; the decoder subject joins in U24.
