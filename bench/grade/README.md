# Grading graded runs (rubric M1–M10)

## Regenerate T2, T3 or T7

From the repository root, run one task:

```sh
offload run --local -- systemd-run --user --scope -q \
  -p MemoryMax=28G -p MemorySwapMax=0 -p OOMPolicy=continue \
  bench/grade/regenerate lz4-c
```

Use `lz4-rust` for T3 or `glm-iround` for T7. The command restores each committed run from
its prepared inputs and archive. It runs M1, M5, M8 and the clean M8 baselines. It also runs
the alternative planting sites and the task's Frama-C or Verus checks. Runs are serial. A
lock prevents overlapping task regenerations in one output directory. Missing Lean claim
receipts, failed Lean surface extraction or missing/duplicate Lean cheat rows make the command
exit 2. For the tool arms, a missing or non-numeric M1 status, a missing or duplicate cheat row
and a missing C0 also make the command exit 2. A complete grading run can still report invalid
proofs. A run's documented check can generate the files that it proves: `manifests/wp-prep-TASK.tsv`
names that step (tool-lz4-c-6: `prepare.py` writes the `*.annotated.c` files that its own
`.gitignore` keeps out of the archive), and `m1-wp.sh` runs it after the rebuild.
Each run starts when at least 16 GB of memory is available. The external memory cap remains necessary:
T3's independent kernel can need more than 20 GB.

Inputs come from `${FVA_BENCH_HOME:-$HOME/.cache/fva-bench}`. The cache must contain the
batch's `inputs/`, `packages-v4.35.0/`, `bin/` and `tools/`. The host must have Lean 4.35.0,
GNU awk, jq, rsync and the runtimes that the archived checks use. T2 also needs the pinned
Frama-C bundle and container image (`scripts/fetch-bench-tools frama-c`). The cache is
read-only to the grading drivers. Archived checks keep their original languages,
including Python; the new grading drivers do not implement grading in Python.

Outputs go to `${FVA_GRADE_OUT:-<repo>/.scratch/grade}/<task>/`:

- `m1.tsv`: theorem replay logs and statuses. `*.claims` records the claim denominator.
- `m5.tsv`: declaration closures. `m5-split.tsv` partitions statement, link/model, tables
  and data. T1's older split is also available through `m5-split lz4-wasm FILE`.
- `m8.tsv`, `m8-base.tsv`, `m8-alt.tsv`: original sites, clean checks and alternate sites.
- `m1-tool.tsv`, `m8-tool.tsv`, `m8-tool-base.tsv`: task-specific tool checks.
- `summary.tsv`: Lean-arm M1, M5 and M8 aggregates. An unconfirmed M1 row is not valid. Tool
  arms: M1 = runs whose documented commands all exit 0; M8 = the main planting site (`M8-<site>`
  = an alternate site), C3 `n/a` left out.
- Per-run projects and logs: inspect them before accepting an M8 catch. A failing clean
  baseline permits credit by cheat-specific name alone, not by exit code.

`manifests/` records the graded run set, documented commands, alternate sites and the
reviewed T2 nonliteral claim citations. A scan is not a claim-coverage judgment: review
`VERIFICATION.md` against `*.claims`. T7's prompted runs 1 and 4 generate observation claims.
Their copies are replayed in sibling `<run>.observation/` projects. Grader helpers stay outside
the M8 project. A forged-proof control is not a claim.

Run the fast driver controls with `bench/grade/check-drivers`. Run `bench/grade/check-fidelity`
to check each task's initial memory and instance lifetime against a stateful fixture. The new
scripts must pass `shellcheck -x` and `shfmt -d`. These controls do not replace the proof checks.

### Model fidelity

`bench/grade/fidelity lz4-c` and `bench/grade/fidelity lz4-rust` replay the published
2,000-case samples against the pinned artifact. Run them in a memory-capped offload slot.
The corpora preserve T2's seeds 27/28 and T3's seed 29 exactly. T2's original generator is
`.scratch/u15/grade/fid-t2/gen.py` (prefix: 27; literal: 28). T3's is
`.scratch/u15/grade/fid-t3/fid.py` (29), with `gen_valid` and `mutate` from
`.scratch/u15/reqcheck/reqcheck.py`. Replay reads the committed input files. The original
generators are not runtime dependencies. Replaying fixed data avoids changing the sample
when the generator's implementation changes. No expected
artifact results are stored. The driver compiles the archived C or Rust model with a small
native I/O fixture, then `Fidelity.lean` builds WAST assertions from its outputs.
Wasmtime checks the return and exact bytes: all caller memory for T2; the returned prefix
for successful T3 calls. `--control` uses the entry model on literal cases (T2), or reduces
model capacities by one (T3); the artifact comparison must fail.

`acsl-lines FILE[:A-B]…` and `verus-lines FILE.rs…` expose the tool-arm line partitions.
Their outputs are measurements, not substitutes for the reviewed statement closure.
`m5-tool lz4-rust` reads the recovered closure selections in `judgments/lz4-rust-m5.tsv`.
Each row cites the published policy and archived source, and pins that source by SHA-256.
The command reports physical statement ranges, Verus model-code counts and generated tables.
It keeps full-file model-code counts and reader-selected physical model ranges separate.
Their selections and line conventions differ. These measurements do not resolve the missing
historical normalization ruling. T2's original
tool partition is not recovered; the command exits 2 when a judgment manifest is unavailable.
`judged lz4-c|lz4-rust|glm-iround` prints the judgment-derived M5 figures: checker scripts per
arm, T2's tool partition from `judgments/lz4-c-m5.tsv`, T3's from `m5-tool`, and T7's checker
code with the check commands that `judgments/glm-iround-checker.tsv` selects in reports. Each
judgment row pins its source by SHA-256; a changed source makes the command exit 2.
M2 extraction checks use `regen-check.sh TASK ARTIFACT MANIFEST`; its outputs include
regeneration, byte comparison, clean check and planted-edit statuses for every file.

## Per-run procedure

Per run `R` = `~/.cache/fva-bench/runs/<arm>-<task>-<i>` (its input dir = `~/.cache/fva-bench/inputs/…` as launched):

1. `FVA_BENCH_AUTH_FILE=<the batch's auth.json> bench/grade/archive R bench/runs/<arm>-<task>-<i>` — record: result.json, metadata.json, gzipped events, the agent's created/changed files.
2. `bench/grade/rebuild <input dir> bench/runs/<…> <scratch dir>` — the project outside the sandbox.
3. M1: list every theorem VERIFICATION.md claims (MAIN reads it); `bench/grade/check-lean <scratch dir> <module> <theorem>…` per module → build, axioms ⊆ {propext, Classical.choice, Quot.sound}, comment-stripped scan for `sorry`/`admit`/`native_decide`/`implemented_by`/`extern`/`debug.skipKernelTC`/`axiom`, leanchecker + con-leche replay. Frama-C/Verus claims: rerun the run's own command with the tool (`bench/tools/frama-c --check-wp …`, `bench/tools/verus …`). Score = valid / claimed.
4. M2: (a) statements about the hash-pinned shipped bytes (fva: `Lifted.lean` + `fva trust` link check; certificates: the output blobs; a run's own extractor, decoder or lifter: MAIN regenerates its generated files from the pinned artifact with the run's script, `cmp`s them with the archived ones, and plants a one-digit change to see the script's check fail); (b) a hand-written model → fidelity vs wasmtime on 2,000 cases (T5: model factors vs both producers' outputs); (c) nothing executable.
5. M3 + M6 (fresh `reviewer` per arm, given README, the official format/edgeR/TMM docs, theorem statements + every definition they use, VERIFICATION.md; calibrated on the v1 decks `git show prototype-link-reach:prototype/bench/verdicts.md` and `…/verdicts-prompted.md`) → per requirement `faithful` | `weaker` | `not proven, reported` | `missing` | `false claim`; over-claim sentences. MAIN rechecks every non-`faithful` verdict.
6. M4 (T1, T4, T5, T6, T7): the defect outcome class, from the run's evidence (MAIN; confirm a "machine-checked counterexample" by its M1 result).
7. M5: trusted surface at equal M3 — (i) requirement statement, (ii) link + model, (iii) checker code the agent wrote; fva arm = `fva trust`'s review surface (FVA's base counted apart).
8. M7: `result.json` (wall_ms, tokens, status; `cpu_*`, `load1_*` = idle-window evidence).
9. M8: `bench/grade/inject <scratch dir> <lean file> <main theorem> <artifact> '<the run's own check command>' <out dir>` → per cheat rc + named; confirm each catch's cause in its log. Tool arms: `bench/grade/inject-tool <scratch dir> <file.c | file.rs> <artifact> '<cmd>' <out dir> [FN]` (Verus: FN = the main proof function; the command names the wrapper by path, e.g. `bench/tools/verus`, since the arm's PATH entry is absent outside its run).
10. M9 (fresh `reviewer`, domain-reader persona: bioinformatician for T4–T6, systems programmer for T1–T3, T7 by subject): per requirement statement `readable` | `readable with effort` | `not readable` + line count read.
11. M10: any machine-checked statement about the shipped artifact (M2 (a)).

Invalid runs (rubric): a model-usage-limit stop (rerun after reset); a read of this repository in `stdout.jsonl` (`zcat stdout.jsonl.gz | grep -c "$(git rev-parse --show-toplevel)"` on the archive; rerun).

## Grading rulings (apply to every arm and task)

- M1: a module export that mixes invalid theorems (`native_decide`, `sorry`) with clean ones can make an independent kernel reject the whole export: recheck the clean theorems alone (`check-lean PROJECT MODULE THEOREM…`). Negative-control files that hold forbidden constructs and are imported by nothing do not count against M1 (prove "imported by nothing" with an import search and a positive control).
- M2 (b): a model that takes inputs = fidelity against the shipped artifact on 2,000 cases (seeded generator, the artifact run by its own harness); an executable model without inputs (a point computation) = (b), point model, checked by the run's own reproducer.
- M2 (a) covers a program the run derived from the hash-pinned bytes with its own tool (a Python extractor, a Lean decoder the kernel checks against embedded bytes, a wasm-to-C lifter) under its own semantics or translation (T1 prompted-3); the results name the extraction and the semantics per run. A statement about the source (C, Rust; a slice or an inlined copy included) = `C source`/`Rust source`, not (a): only the untrusted compiler links source to bytes, so a byte-identical rebuild is noted, not credited; M10 = no.
- M3: a statement over a replay-supplied intermediate (for example the kept genes copied from a float run) whose relation to the documented method is unproved = `weaker`; a sound refutation of a false requirement = `not proven, reported`.
- M3 on a task without a known defect (T2, T3): `faithful` = the statement covers the requirement's whole domain (every size, placement and byte content the README allows); `weaker` = a proven statement about the requirement's own observable (the access trace for a memory requirement, the return value and output for a decoding requirement) on a sub-domain (bounded sizes, fixed blocks, a loop bound), under an extra hypothesis, or for a part of its conclusion (writes alone), disclosed or not, and an undisclosed narrowing is also an M6 finding; `not proven, reported` = no such statement, only a different observable the requirement implies (final-store or guard-byte equality after a call says nothing about reads, nor about writes undone before the end), with the requirement reported open, as for T5's prompted 1 (a normalization property); `false claim` = a requirement called verified with no supporting statement (executed tests, fuzzing and differential runs are evidence, not proof) or with a false one. The program a statement is about (the shipped bytes, the source, a model) is M2's, and leaves M3 unchanged.
- M3 program identity: `faithful` and `weaker` need a program the statement constrains: the shipped bytes, the source, or an executable model the run wrote (M2 (a), the source, (b), whose 2,000-case fidelity gives a model-level `faithful` its meaning). A formalization made only of specification functions (Verus `spec fn`s, Lean definitions with no decoder program) restates the requirement and constrains no decoder's return or output: `not proven, reported` where the report leaves the requirement open.
- A theorem a run's check generates into a hidden directory (e.g. `.verification/Observation.lean`, binding an executed result to a Lean statement) is not a Lake module: M1 checks it as a module copy in a separate directory, M8 plants at the first cited theorem outside such files, and a file that only holds the check's own controls (forged-proof fixtures) carries no claim.
- M5 + M9: input and output literal tables (count matrices, copied factor values) are data, counted apart from code lines (`bench/grade/Surface.lean`: more than 20 lines of 90 % digits and separators), as FVA blobs are.
- M8: the cheat goes into the first theorem the report cites outside a lifted module; where that theorem is a support lemma the run's own check never covers, also plant at the first Spec-claim proof and report both; where it sits in a module a run's script writes (an extracted or embedded artifact module, a generated case table), also plant at the first cited theorem outside such modules and report both, since a check that compares the file with a regeneration catches any edit there (the log's cause decides each row; no such theorem → say so); a catch needs rc ≠ 0 from the cheat (not a syntax error) or a cheat-specific token, and every documented check gets a clean baseline (`C0`).
