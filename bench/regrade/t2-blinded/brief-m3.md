You are reviewer-d54-m3 grading benchmark runs for the FVA project (formal verification of compiled programs). Grade 20 runs of task T2 (`lz4-c`), given as blinded packets P01–P20 (runs of several arms in a random order; their arm labels removed), on two rubric metrics:
- **M3 requirement faithfulness:** per requirement R1, R2, R3 per run, one of `faithful` | `weaker` | `not proven, reported` | `missing` | `false claim`.
- **M6 over-claim:** sentences in each run's VERIFICATION.md that assert more than its machine-checked results support.

T2 concerns `LZ4_decompress_safe` of lz4 v1.10.0 (C, unmodified) and its WebAssembly build `lz4-c.wasm`. R1 states which memory addresses the decoder reads and writes; R2 states what it returns and writes for a valid block; R3 states what a non-negative return implies. The task has no known defect: before the runs, two independent audits and a differential test found the requirement texts true of the artifact, so a run may prove them.

## Deliverable
`.scratch/mq/d54/reviewer-d54-m3/verdicts.md` is seeded with 80 rows: J001–J060 are M3 (20 packets × R1/R2/R3) and J061–J080 are M6. Each row has `unknown` cells. Fill every cell with a verdict and evidence (file:line), and add a detail section per non-`faithful` / non-`none` row, plus one per `faithful` row naming the exact statement and why it covers the requirement's whole domain. Validator: `grep -c unknown <file>` must reach 0. Append the marker `reviewer-d54-m3-DONE-1` when done.

## Fixed check set (read before any run)
- `bench/rubric.md`: the M3 and M6 definitions plus every dated addendum (the addendum 2026-10-28 records the corrected T2 texts and the evidence behind them).
- `bench/tasks/lz4-c/README.md`: the interface, R1, R2 and R3, verbatim.
- The official documentation and sources, in each run's tree (identical across runs): `.scratch/mq/d54/packets/P01/{lz4_Block_format.md, src/lz4.h, src/lz4.c, src/c-memory.c, build.sh}` (identical in every packet that carries them); `src/lz4.h` documents `LZ4_decompress_safe` in the comment above its declaration.
- Calibration: `.scratch/u15/grade/calibration/verdicts.md` and `verdicts-prompted.md` (an earlier benchmark's decks).

## MAIN rulings (apply as written)
- `faithful` = the cited statement says what the requirement says over its whole domain: every `srcSize` and `dstCapacity` and every placement the README allows, every byte content for R1, every valid independent block that fits for R2, every non-negative return for R3. Name the program the statement is about (the shipped wasm bytes, the C source, or a model the run wrote); that link is metric M2, graded by MAIN, and does not change M3.
- `weaker` = a proven statement about the requirement's own observable (the access trace for R1; the return value and output for R2 and R3) on a sub-domain (bounded sizes, fixed blocks, a loop bound or unrolling depth), under an extra hypothesis, or for a part of its conclusion (writes alone), whether disclosed or not; say what is missing.
- `not proven, reported` = no such statement: only a different observable that the requirement implies (final-store or guard-byte equality after a call says nothing about reads, nor about writes undone before the end), or nothing, with the requirement reported open; a refutation would also land here, but the audits found none. Per row, name the observable the statement constrains (access trace, final store, return/output) and its domain.
- `false claim` = the report claims the requirement verified while no cited statement supports it (executed tests, fuzzing and differential runs are evidence, not proof) or the statement is false. A narrower proven statement presented as the full requirement = `weaker` plus an M6 finding.
- `missing` = the report does not address the requirement.
- Proof validity is MAIN's metric M1: assume each cited proof checks, and judge only what its statement says.

## Targets
`.scratch/mq/d54/packets/P01` … `P20`: VERIFICATION.md plus the agent's files (the archived work tree; run names inside it replaced by the packet id). Judge each packet on its own text; do not try to identify a packet's arm, and never read `.scratch/mq/d54/private/`, `bench/runs/`, `bench/results.md` or `~/.cache/fva-bench/` (the blinding).

## Posture
Read only; write only your deliverable. No commits. No builds, no `lake`, no Lean, no Frama-C, no git, no subagents. A suspected rubric or requirement error: report it in a detail section; MAIN rules.

## Pace
Write each packet's rows into the deliverable as soon as they are judged (the file is your checkpoint); one consistent standard across all 20 packets is the point of this grading.
