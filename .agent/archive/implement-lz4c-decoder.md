# IMPLEMENT — lz4 C decoder proof + proof scaling (U19 checkpoint 2)

Request (verbatim): Scope: U19 checkpoint 2, the decoder proof. Finish line: FVATest/Subjects/Lz4C/Spec.lean states R1–R3 for LZ4_decompress_safe on the shipped lz4-c.wasm, as formalized in docs/contracts/U19-decoder-spike.md (Checkpoint 2). fva trust passes on it, default and --paranoid, with the review surface pinned in scripts/test-subjects. R1 meets D52's acceptance. Milestones, each committed gate-green: (1) R1 whole-domain, footprint plus termination; (2) R2 and R3. If a milestone shows the full theorem out of reach, stop with the evidence and ask me: a narrower claim or a source-level link, per .agent/archive/maintain-bench-direction.md. Start from the contract inventory. Begin with I4 (separate ordered-copy contracts for the compiled memcpy and memmove, plus one wildcopy loop composed with them), and scope the I7 one-sequence format invariant alongside. Measure first-use vs reuse effort, export and replay growth, and theorem coverage (.agent/archive/u19/scientist-1-e1.md E4). Settled, do not reopen: the stack and wasm-lift link (Decisions), the footprint vocabulary as shipped, and the checkpoint-1 proofs. Open and costly to reverse, so it gets the IMPLEMENT orientation steps (research, a check-graded spike, consultants): the proof-scaling method. The options are hand stepping (provisional), refinement to a model, or automated block summaries (D9, decompilation-into-logic style). Out of scope: lz4_flex, the encoder, bench v3

## Rows
- [x] c736868 … 4085c4e seam + composition: frozen spike statements S1–S5, `Model.lean` (differential vs the binary, 103,070 pairs, 0 mismatches) + `ModelProof.lean`, cutpoint statements `Seg.lean`, `Prefix`/`Match`/`Sim`/`Top` = R1–R3 from the cutpoints, `Cut/{Entry,ErrRet,SegA}` by stepping; tester-1's acceptance suite (`Spec`, `Accept`, `Refute/*`)
- [x] 448f18e ExtL1B + SegA (`Cut/ExtB`, checkpoint 1's route D with the bound exit kept)
- [x] 2865183 gate: subject trust runs side by side
- [x] 51d6227 U20 proof-scaling method: engine C (user ruling)
- [x] 27a2d5e U21 merge engine C (Eval/), `Proof.lean` R1–R3, trust PASS both modes
- [x] 3347289 U22 every subject in default + `--paranoid` (`scripts/subject-matrix`), lean4lean's heartbeat limit = a decline
- [x] 406e5ed U23 factored spec (`Call.lean`, 76 lines), `SpecEq` equivalences, empty-buffer witnesses, K1
- [x] e8dfc1c U24 milestones 1 + 2: the decoder subject in the gate (surface 76), full gate green
- [x] (closing commit) U25 close: U19 contract results (coverage ledger, effort, growth), README, AGENT.md, review ledger, D9/D52 closed

## Outcome
- R1–R3 on `LZ4_decompress_safe` in the shipped `lz4-c.wasm`, for every input of the domain (buffers in 131072…2097151, lengths < 2^31, disjoint unless one is empty): `fva trust` PASS in default and `--paranoid` mode in the full gate; review surface 76 lines; D52 met (R1 = `CallWithin` on a lifted subject).
- Method (U20): rule 3 inconclusive (C/D+ cross on lines; V dominated); engine C chosen by the user for its build cost (about half of D+'s; S5 work 28 vs 83 s); production: C proved SegB (203 lines) and SegD (655 lines); D+'s SegB (257) + partial SegD archived.
- Gate: every subject now runs both trust modes; the first such run exposed lean4lean's heartbeat limit on Lz4Wasm's 433-step encoder evaluation (now a decline, as its recursion limit).
- Measurements: first-use vs reuse, export + replay growth and the coverage ledger in the U19 contract (Checkpoint 2 results); U20's in its contract + `.agent/archive/u20/`.

Teammates: navigator-1..3 (interpretation), researcher-1..4 (method candidates), scientist-1/2/3 (spike design, round-2 design, results appraisal), spike-c / spike-d / spike-v (arms C / D+ / V), tester-1 (acceptance suite), consultant-1..5 (ruling), consultant-6..12 (plan verdict + pre-mortem), consultant-13 (U22 contract), tester-2 (U22 battery), reviewer-1 (K1 spec audit); advisor (ruling + question batch).
