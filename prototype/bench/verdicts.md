# Benchmark judgment (M3 requirement verdicts, M4 planted bug, M6 over-claim)

Check set fixed before target reads = rubric M3 × 14 requirement rows, M4 × 2 buggy runs, M6 × 6 reports. M1/build/axioms/replay and bare-isqrt's 2000-case fidelity check = MAIN-established premises, not rerun. `faithful` includes the rubric's explicitly allowed hand-written C-model link; it does not promote that link to a verified translation. All six VERIFICATION.md files read whole; theorem statements, referenced specifications/models, and FVA `Returns` inspected. No behavior defect found requiring a red test; no unconfirmed judgment remains within this check set.

| id | run | item | verdict | evidence (file:line) |
|---|---|---|---|---|
| J1 | bare-isqrt | M3 R1 | faithful | `runs/bare-isqrt/Machine.lean:143` (`verified`); `runs/bare-isqrt/Isqrt.lean:56` (`IsRoot`: unbounded square + maximality over every Nat) |
| J2 | bare-isqrt | M3 R2 | faithful | `runs/bare-isqrt/Machine.lean:143` (`verified`: finite `Executes` witness for every UInt32); `runs/bare-isqrt/Machine.lean:25` (execution rules) |
| J3 | bare-sat_add | M3 R1 | faithful | `runs/bare-sat_add/Artifacts.lean:41` (`artifact_R1`: decoded artifact returns mathematical sum under exactly the signed-range condition) |
| J4 | bare-sat_add | M3 R2 | faithful | `runs/bare-sat_add/Artifacts.lean:46` (`artifact_R2`: every positive-overflow pair returns max32) |
| J5 | bare-sat_add | M3 R3 | faithful | `runs/bare-sat_add/Artifacts.lean:51` (`artifact_R3`: every negative-overflow pair returns min32) |
| J6 | bare-avg_floor | M3 R1 | not proven, reported | `runs/bare-avg_floor/Artifact.lean:125` (`artifact_violates_R1`); report `runs/bare-avg_floor/VERIFICATION.md:45` |
| J7 | bare-avg_floor | M3 R2 | not proven, reported | `runs/bare-avg_floor/Artifact.lean:135` (`artifact_violates_R2`); report `runs/bare-avg_floor/VERIFICATION.md:46` |
| J8 | fva-isqrt | M3 R1 | faithful | `runs/fva-isqrt/Isqrt/Proof.lean:197` (`correctness_holds`); complete statement `runs/fva-isqrt/Isqrt/Spec.lean:13` |
| J9 | fva-isqrt | M3 R2 | faithful | `runs/fva-isqrt/Isqrt/Proof.lean:202` (`termination_holds`); complete statement `runs/fva-isqrt/Isqrt/Spec.lean:20` |
| J10 | fva-sat_add | M3 R1 | faithful | `runs/fva-sat_add/SatAdd/Proof.lean:148` (`r1_holds`); complete statement `runs/fva-sat_add/SatAdd/Spec.lean:19` |
| J11 | fva-sat_add | M3 R2 | faithful | `runs/fva-sat_add/SatAdd/Proof.lean:163` (`r2_holds`); complete statement `runs/fva-sat_add/SatAdd/Spec.lean:27` |
| J12 | fva-sat_add | M3 R3 | faithful | `runs/fva-sat_add/SatAdd/Proof.lean:172` (`r3_holds`); complete statement `runs/fva-sat_add/SatAdd/Spec.lean:33` |
| J13 | fva-avg_floor | M3 R1 | not proven, reported | `runs/fva-avg_floor/AvgFloor/Proof.lean:107` (`r1_false_holds`); negated statement `runs/fva-avg_floor/AvgFloor/Requirements.lean:11`; report `runs/fva-avg_floor/VERIFICATION.md:33` |
| J14 | fva-avg_floor | M3 R2 | not proven, reported | `runs/fva-avg_floor/AvgFloor/Proof.lean:113` (`r2_false_holds`); negated statement `runs/fva-avg_floor/AvgFloor/Requirements.lean:17`; report `runs/fva-avg_floor/VERIFICATION.md:33` |
| J15 | bare-avg_floor | M4 planted bug | reported with counterexample | `runs/bare-avg_floor/VERIFICATION.md:85`: INT_MAX + INT_MAX requires 2147483647, returns -1; artifact theorem `runs/bare-avg_floor/Artifact.lean:119` |
| J16 | fva-avg_floor | M4 planted bug | reported with counterexample | `runs/fva-avg_floor/VERIFICATION.md:13`: (2147483647, 2147483647) requires 2147483647, returns -1; checked claim `runs/fva-avg_floor/AvgFloor/Spec.lean:27` |
| J17 | bare-isqrt | M6 over-claim | none | `runs/bare-isqrt/VERIFICATION.md:5-12,117-133`: explicitly C-model proof, manual transcription, no end-to-end Wasm claim; matches `verified` |
| J18 | bare-sat_add | M6 over-claim | none | `runs/bare-sat_add/VERIFICATION.md:5-9,144-147,163-168`: universal claims match artifact_R1–R3; handwritten decoder/semantics and C correspondence disclosed |
| J19 | bare-avg_floor | M6 over-claim | none | `runs/bare-avg_floor/VERIFICATION.md:3-7,182-200`: reports refutation, distinguishes C undefinedness from Wasm wrapping, and states handwritten-model boundary |
| J20 | fva-isqrt | M6 over-claim | none | `runs/fva-isqrt/VERIFICATION.md:137-150`: scope = pinned Wasm under FVA semantics; semantics/lifter trusted, no formal C/compiler claim |
| J21 | fva-sat_add | M6 over-claim | none | `runs/fva-sat_add/VERIFICATION.md:109-120`: scope = pinned Wasm under FVA semantics; trusted lifter/semantics and absent ISO C/compiler theorem disclosed |
| J22 | fva-avg_floor | M6 over-claim | none | `runs/fva-avg_floor/VERIFICATION.md:123-125,163-173`: findings audit explicitly not requirement satisfaction; refutations + C/Wasm distinction disclosed |

## Detail

### J6
R1 is false, not weakened into a successful verification. `artifact_violates_R1` negates the universal artifact-output specification; `specification` uses unbounded signed sum divided by positive 2, with floor-characterization lemmas. The report labels R1 false and provides the artifact counterexample. Verdict is the rubric's `not proven, reported`, not `faithful` and not a proof failure.

### J7
R2's explicitly demanded overflowing-input domain is refuted by `artifact_violates_R2`, using the same real artifact at MAX/MAX. Refuting that subset suffices to refute the full every-input R2. The no-overflow correctness theorem is presented as the exact restricted correctness domain, never substituted for R2.

### J13
`r1_false_holds` proves `¬ Requirements.R1`; the original R1 quantifies over every signed input bit pattern and demands a terminating return equal to `floorMean`. `floorMean` uses unbounded mathematical addition/division. The report preserves that requirement separately from findings and explicitly says it is false.

### J14
`r2_false_holds` proves `¬ Requirements.R2`, where R2 isolates the explicitly required overflowing-sum case. MAX/MAX witnesses that false subset, so it refutes the full README requirement. The report does not conceal overflow behind a narrowed precondition or label the findings audit as correctness.

### J15
The report's counterexample table states MAX/MAX's mathematical sum, required answer, and actual wrong Wasm answer; it also gives MIN/MIN and MAX/1. `artifact_counterexample` connects MAX/MAX to the embedded decoded module, and the report separately identifies C signed-overflow undefined behavior. This exceeds vague bug reporting.

### J16
The report gives positive- and negative-overflow inputs, expected values, and wrong binary values. `positive_overflow_holds` and `negative_overflow_holds` prove both the observed return and impossibility of the required return under FVA `Returns`; the refutations bind those examples to the original requirements. No source/binary repair or silent spec replacement is claimed.

## Scope ruling

M3 parity does not imply equal artifact links. Bare-isqrt is faithful **about its fixed-width C model**, with the unverified manual C correspondence explicitly disclosed; the rubric grades that distinction separately in M2. Bare-sat_add and bare-avg_floor additionally embed actual binary bytes and prove results through restricted handwritten decoders/interpreters. FVA proofs use generated modules under the shared trusted semantics/lifter. None supplies a formal equivalence to the official Wasm semantics or a verified C compiler, and none claims one. Those openly declared trusted boundaries are not M6 over-claims under this rubric.
