# scientist-3 — U20 results appraisal

| id | claim / question | verdict (supported / partly / unsupported / open) | evidence (file:line or measurement) | implication for the ruling |
|---|---|---|---|---|
| E1 | Eligibility per arm under contract rule 1 + 4 (proofs, axioms, both default checkers accept, replay ≤ 10 min, module builds ≤ 10 min) | supported | `measure/prep-{c,d}.log`, `prep-v-plain.log`: five exact roots + standard axioms each; `m2.tsv` 324/324 rc 0; `m3.tsv` every export/replay rc 0. Observed module maxima, runs 1–3: C 18.98, D+ 79.30, V 174.48 s; max root replay 62.56/63.19/62.88 s. | All three eligible on the frozen slice. Both SegC roots also accepted/replayed. V's 40-warning `--wfail` failure is separate gate hygiene; default acceptance passed. Not whole-decoder `fva trust`. |
| E2 | Rule 3 verdict over round 1 with (c)/(e) included | supported | Contract `:32–36`; P1/P4 + `m2.tsv`/`m3.tsv`: C total/S5 = 1650/368, D+ = 1682/341, V = 2448/663; C/V and D/V every runtime guard <2. | C and D+ each dominate V; C/D+ cross on necessary line coordinates ⇒ no lone dominant arm. Round 1 remains inconclusive; a C choice is a qualitative project-local policy ruling, not the rule-3 winner. |
| E3 | What round 2 (SegC: lines, M0, D3 split, reuse inventories) supports about cost on the remaining decoder | partly | C/D raw D3 maps: 247/287 total = 73/67 execution + 58/42 model + 116/178 plumbing; 1366/1930 s reported contended M0. Code: C `SpikeC/SegC.lean:48–74,143–205`; D `SpikeD/SegCBase.lean:52–64`, `SegCLoop.lean:11–97`; main `Cut/SegA.lean:128–154`. | Both extend unchanged engines to a symbolic-byte loop. C's 40-line advantage is plumbing-heavy, not an identified evaluator effect. ExtL1B is broader (reachable overflow); SegB/SegD require call/memory/table paths absent from SegC. No decoder-wide cost forecast. |
| E4 | Build/replay cost (M2/M3, r2) differences: real, within noise, or confounded (sequential M2 on CPU 7 with interleaved arms; host load; frequency scaling) | partly | P3–P5, all measurement rows: M2 Σ module medians C/D/V = 120.51/226.03/622.38 s; observed totals C 120.39–127.79 < D 206.46–253.46 < V 528.29–1142.94. S5 changed-module medians C/D = 28.28/83.42 s. M3 replay medians C/D LC 52.44/53.73, CL 60.37/63.00 s; r2 LC spreads 19.56/65.71 s. | C has materially cheaper observed elaboration, including whole S5 work; uncontended effect size is not identified. Replay costs are similar, not proven equal; r2 timing ranks are confounded. Minima are sensitivity summaries, not contention correction. Full-decoder replay projection remains unidentifiable and cannot decide. |
| E5 | The strongest case for each of C and D+ from this evidence, and what it cannot show | partly | E1–E4/P5; C `BlockEval.lean:65–143`, D `Direct.lean:132–171`; current `ruling-draft.md:88–130`; shared `Cut/ExtB.lean:229,249`. | Provisional C for SegB/SegD is justified as policy: materially cheaper observed elaboration + bounded readiness, modest author-confounded size/time benefits, no decisive replay penalty. D+ retains smaller S5 source + continuity. Later subjects = a default to test, not validated scaling; failure history does not establish C's tail-risk superiority. |
| E6 | The single measurement or check that would most change a C-vs-D+ ruling, if any | supported | E1/P4: planned C+D final-root check passed (2 exports + 12 replays, 716.39 s); P5: whole-S5 scope; draft `:132–135`. | No extra prerequisite for provisional C. Highest-leverage optional falsifier of its main timing ground = quiet, paired, unchanged-artifact S5 changed-module M2, CPU + sibling idle; ~447 s execution scenario, waiting extra. Not run; no new proof race. Reversal must track real cutpoint/replay/budget failure, not S5's “rate” or a mandatory two-block count. |

## Detail

Complete: E1–E6 adjudicated against the frozen protocol, harvested proofs, 394 measurement observations and the completed ruling draft. Provisional C is justified as a project-local policy, not a dominant or causally superior method. This appraiser ran text/data probes only; MAIN's archived acceptance/replay outcomes are identified separately.

Paths: `Contract` = `/home/eturkes/Projects/fva/docs/contracts/U20-proof-scaling.md`; `C/…`, `D/…`, `V/…` = `/home/eturkes/Projects/fva/.scratch/worktrees/spike-{c,d,v}/…`; `data/<arm>/…` = `/home/eturkes/Projects/fva/.scratch/u19c2/spike-<arm>/…`; `measure/…`, `researcher-4.md` = under `/home/eturkes/Projects/fva/.scratch/u19c2/`; `Seg.lean`, `ExtDirect.lean`, `Cut/…`, `Spike{C,D,V}/…` = under `FVATest/Subjects/Lz4C/` in main or the named arm. Other source paths = relative to `/home/eturkes/Projects/fva/`.

### E1

**Finding E1a — C, D+, V all meet frozen eligibility.** Exact `MainAccept.lean:11–20` examples match S1–S5; all three worktrees' Copy/Short hashes match the contract. MAIN's successful acceptance logs report exactly the standard axioms for each root: C `measure/prep-c.log:1871–1876`, D `prep-d.log:1876–1881`, V `prep-v-plain.log:2127–2132`. Both default kernels returned rc 0 on every final-root replay (`m3.tsv`, tags `c-s1-5`, `d-s1-5`, `v-s1-5`, three repetitions × two checkers). All 324 M2 rows = rc 0, every expected module/run present (P3).

| arm | new modules | largest measured module observation, runs 1–3 | largest observation including warm-up | largest S1–S5 replay, either checker | eligibility |
|---|---:|---:|---:|---:|---|
| C | 21 | 18.98 s | 37.38 s | 62.56 s | eligible |
| D+ | 23 | 79.30 s | 79.30 s | 63.19 s | eligible |
| V | 37 | 174.48 s | 174.48 s | 62.88 s | eligible |

Resource eligibility uses these **observed maxima**, not the slowest-module medians (17.6/64.4/88.2). Every maximum remains below 600 s. Absolute replay is already below the incremental-replay ceiling, so no baseline-time subtraction is needed for this conservative operational acceptance. Report status depends on the named frozen artifacts/harness, not an estimate of future-build success.

**SegC acceptance:** exact examples + standard axioms (`r2-prep-c.log:1841–1842`, `r2-prep-d.log:1856–1857`); all 14 r2 export/replay rows and all 16 r2-M2 rows rc 0. Measured module maxima C/D = 23.62/51.40 s (including warm-up 47.39/65.78); max replay = 99.78/116.95 s. Heavy contention does not undo these observed acceptances; it does undermine comparative timing inference (E4).

**Limits / distinction.** V's `prep-v.log` has 40 `warning:` lines and `--wfail` failure; ordinary acceptance succeeded. This is a separate shipping/gate-hygiene deficit, not a failed formal root or a reason to alter eligibility retrospectively. Checker acceptance on these roots does not prove whole-decoder R1–R3, default/paranoid `fva trust`, a full gate, checker-canary behavior or provenance of every runtime binary. Those checks were not rerun by this appraisal. Lean/tool/backend pins and canary histories were not independently audited; source/hash/log/TSV evidence is the basis stated here.

### E2

**Finding E2a — no lone dominant arm after runtime + eligibility checks.** Frozen rule 3 is conjunctive: C total 1650 < D+ 1682, but C S5 368 > D+ 341. V's 2448/663 exceeds both on both line coordinates. All three are eligible (E1). Runtime guards confirm both C and D+ dominate V; neither can dominate the other. This is exactly the contract's inconclusive → qualitative-ruling route, not failure of the experiment.

| comparison | largest stage-M0 ratio X/V | M2 Σ-median ratio X/V | conservative observed total max(X)/min(V) | replay min(X)/max(V), LC / CL | rule-3 outcome |
|---|---:|---:|---:|---:|---|
| C / V | 1.1706 | 0.1936 | 0.2419 | 0.8032 / 0.9424 | C dominates V |
| D+ / V | 0.9784 | 0.3632 | 0.4798 | 0.8438 / 0.9957 | D+ dominates V |

Each runtime guard is below 2; P4 recomputes the contract's replay range rule separately for both checkers. This conclusion survives Σ-minimum versus Σ-median build summaries and even the conservative run-total comparison shown. V's warning cleanup is not needed to produce the domination result. No metric weighting or new aggregate score is introduced.

**Accounting sensitivity.** Contract uses MAIN's 1650/1682 stage sums; arm reports expose one changed existing line each (`data/c/report.md:181`; `data/d/report.md:197`), giving 1651/1683 when charged again and D S5 342. Crossing remains. Even ±1 line *per stage per arm* leaves ≥22 total lines and ≥25 S5 lines of crossing (P1). These are small artifact-size differences, not statistical effects or a minimum-important-difference test. No new combined round-1+SegC dominance test is authorized (`Contract:62–66`).

**Limits.** New+changed accounting is not independently regenerated with Lean's parser here; P1 checks both reported variants. Source counts are not active effort, proof complexity, maintenance cost, or human-review surface. Runtime repetitions characterize these artifacts under the recorded host conditions, not a distribution of authoring attempts. The round-1 inconclusive result cannot become a measured engine-class victory by selecting a favorable secondary ratio.

### E3

**Finding E3a — bounded transfer succeeds; a causal engine effect is unidentified.** Both exact `SegC` proof bodies use their assigned engine for the loop, not a borrowed execution theorem: C `c_loop` (`C/FVATest/Subjects/Lz4C/SpikeC/SegC.lean:143–205`) batches 13/24 reference steps through `wasm_eval`; D `cm_loop` (`D/FVATest/Subjects/Lz4C/SpikeD/SegCLoop.lean:11–97`) uses `wasm_dstep` around an ordinary fuel induction. First-green logs print standard-only axioms (`data/c/round2-build-007.log:1–3`; `data/d/build-80.log:1–4`). Both worktree `Seg.lean` hashes equal frozen `ff4cbe58…07001`. MAIN's exact-root acceptance + both default-kernel replays now pass (E1).

**Observed magnitude + rival.** C uses 40 fewer lines (13.94% of D's 287), with reported contended M0 1366 versus 1930 s (29.22% shorter). Neither percentage estimates an engine effect. Raw partitions reconcile: D−C = −6 execution, −16 model, +62 plumbing = +40 total (P2). C actually has *more* reported execution+model source (131 versus 109); its total advantage lies in endpoint/state representation. C concretizes all 19 locals once (`SegC.lean:48–74`); D preserves an abstract local list through `CMInv.update` and reconstructs slot facts (`SegCBase.lean:52–64`; `SegCLoop.lean:47–59,66–82`). Both are legitimate implementation choices, but neither is intrinsically forced by block evaluation versus stepping. Holding only file scaffolding out leaves a 29-line gap; this sensitivity explains the metric, it does not replace the frozen full-cost accounting.

D3 categories are author-labelled semantic allocations, not blinded measured effort. C charges footprint discharge to execution; D's execution/plumbing boundary is not identical. A six-line execution gap cannot support even a local engine-glue winner without a common classifier. Single author × engine pairing, unequal inherited libraries/context, waits and host contention remain fully confounded. Repeated machine timings will not replicate proof authoring. Five staged tasks plus this transfer are correlated trajectory observations, not six independent trials; no significance test or power claim is warranted. Exact resumed model/backend/effort + per-arm contention were not audited.

**Finding E3b — reuse is real, inventory counts are incommensurate.** C adds a complement lemma + a simp registration, D a complement lemma + more module scaffolding; neither reports a new engine/soundness bridge (`data/c/report.md:223–225`; `data/d/report.md:233–235`). C's inventory = 47 **direct** project theorem constants (161 with core/Mathlib); D's = 876 **transitive**, including generated auxiliaries (`:263` and `:252`, respectively). These numbers cannot measure relative dependency burden, reuse, or maintainability. Inspected SegC source calls no checkpoint extension-loop execution lemma. D reports reading `Cut/SegA.lean` but using none of its lemmas (`data/d/report.md:256`): absence of theorem reuse does not rule out orientation help; actual attention/exposure is unconfirmed. Do not call carryover absent in a universal sense.

**Finding E3c — prediction by remaining obligation, not per instruction.**

| target | supported transfer inference | what the spike does not establish |
|---|---|---|
| `ExtL1B` | Symbolic-byte sentinel/bound loops with locals/label preservation are feasible in both engines. Existing `ExtDirect` already supplies the broad loop pattern. | `Cut/SegA.lean:145–154` has arbitrary `acc < 2^31`, arbitrary `lim+1<2^32` with no 2 MiB memory cap, and an exact bound-exit equality `p+k=lim` (`:128–141`). SegC is restricted to 2 MiB and both new proofs prove overflow impossible. Example arithmetic `acc=2^31−1`, next byte=1, `p+1≤lim` makes ExtL1B's overflow reachable. A SegC-derived proof would need a reachable-overflow branch + stronger exit witness; SegC is not a drop-in proof or calibrated cost forecast. MAIN's shared `Cut/ExtB` now supplies this obligation from checkpoint 1. |
| `SegB` | Prior S1/S2 + S3/S5 provide call composition, buffer separation, wildcopy and local-update patterns (`Seg.lean:52–97`). | SegC has no calls or stores. The near-end memmove/return path, general literal path and exact offset-byte preservation are not exercised by this transfer. No C/D cost ranking follows. |
| `SegD` | S4 + S5 provide match-copy and join patterns; SegC adds another data-dependent control example. | Offset<8 tables, prologue writes, near-end wildcopy + byte tail, error after writes and final head restoration remain distinct (`Seg.lean:181–244`). This is the least represented remaining cutpoint; tiny read-only SegC cannot certify its scalability. |

Current remaining work = SegB/SegD. MAIN's `Cut/ExtB.lean:229,249` (`448f18e`) supplies `extL1B : ExtL1B` and `segA : SegA` by retaining checkpoint 1's stronger bound invariant. These declaration/type bytes and commit were checked, not rebuilt here. This is common work available to either engine, not an extra D+ arm observation or a cost charge against C. It confirms the practical importance of distinguishing proof-domain transfer from shared-baseline reuse.

These predictions concern the fixed decoder/profile. They do not establish future-subject scaling, automatic invariant discovery, or lower review-surface size. Both proof engines still return the same `Until`/`Within` interface, so existing cutpoints can compose without being rewritten into the chosen engine.

### E4

**Finding E4a — complete data, improved controls; not a quiet host.** P3 checks all 394 observations: M2 324 (81 modules × four runs), M3 40 (16 exports + 24 replays), r2 14 (two exports + 12 replays), r2-M2 16 (four modules × four runs). Every rc = 0; all expected module/run and tag/checker/rep combinations occur. Warm-up run 0 is excluded from comparative build summaries.

Harness amendment before M3/r2 starts, per MAIN's directive, confirmed in source: CPU-pinned `xport` (`measure/measure.sh:96–103`), replay rounds interleaved across arms in rotated order (`:105–117`), repeated all-new-SegC-module M2 with alternating arm order (`:156–170`). This addresses the original export-affinity/replay-batching/scope gaps. M2 uses its original sequential/interleaved CPU-7 design. Shared checker invocation is constant across arms; no evidence of cross-arm checker-command drift. Actual binary/version hashes are not a retained measurement manifest inspected here.

MAIN reports i7-8650U, four cores/eight threads, powersave/shared turbo, CPU 7 sharing an SMT core with CPU 3; other work remained active (`scientist-3/phase-b-message.txt`, host facts). Affinity reserves neither the logical CPU nor its sibling or turbo budget. These host-history facts are supplied observations, not independently recovered from per-process telemetry. Data show the corresponding nonstationarity; “controlled affinity” must not become “isolated load.”

**Finding E4b — C's measured elaboration advantage is substantial; the counterfactual uncontended ratio is not identified.** Seconds; Σ medians/minima operate module-wise, whereas each run-total sums that run's whole arm. They are different estimands: Σ medians need not equal any realized build or median run-total.

| workload | modules | Σ module medians | Σ module minima | complete run totals 1 / 2 / 3 | median of run totals | peak RSS KiB, warm-up included |
|---|---:|---:|---:|---|---:|---:|
| S1–S5 C | 21 | 120.51 | 118.19 | 120.39 / 124.36 / 127.79 | 124.36 | 2,837,316 |
| S1–S5 D+ | 23 | 226.03 | 205.47 | 206.46 / 252.43 / 253.46 | 252.43 | 3,131,592 |
| S1–S5 V | 37 | 622.38 | 526.62 | 648.63 / 1142.94 / 528.29 | 648.63 | 3,172,332 |
| SegC C | 1 | 23.19 | 19.69 | 23.19 / 19.69 / 23.62 | 23.19 | 2,852,176 |
| SegC D+ | 3 | 56.06 | 55.69 | 69.56 / 56.05 / 55.70 | 56.05 | 2,837,152 |

C's largest measured S1–S5 total (127.79) is below D's smallest (206.46); D's largest is below V's smallest. C/D = 0.5332 on Σ medians and 0.5752 on Σ minima; even max(C)/min(D) = 0.6190. S5 root observations C 16.96/18.98/17.24 versus D 64.36/79.30/63.57 s show an even larger separation, 0.2679 median ratio. Differences exceed the observed within-artifact spread; the cheaper observed artifact is not a tiny-noise winner.

**Targeted rival check P5 — did C move expensive S5 work into prebuilt imports?** Count every S5-checkpoint added/changed module, including D's changed `Direct` tactic and C's acceptance wrapper. C: five modules, Σ medians 28.28 s, run totals 28.04/29.87/28.45; D: seven, 83.42 s, totals 81.92/102.29/88.75; V: twelve, 230.39 s, totals 230.62/430.91/212.32. The C/D ratio is 0.3390, less dramatic than root-only 0.2679 but still a large gap. Thus module factoring alone does not explain this artifact difference. Root-only comparisons would misleadingly make V's 5.21 s S5 wrapper look cheapest; whole added-module cost is load-bearing.

**Contention sensitivity, not correction.** D totals rise from 206.46 to 252–253 s, V from 648.63 to 1142.94 then 528.29; C remains 120–128. The reported host contention fits this pattern, but neither causal slowdown nor its exact magnitude is recoverable. Σ minima combine each module's most favorable observation, possibly from different load regimes; they are downward-selected composites, not estimates of a common uncontended run. Rotating order mitigates steady drift, not sudden sibling saturation. Repetition n=3 cannot estimate tail risk or establish the speed of another author's implementation. The observations support a practical artifact preference under these sampled conditions, not “C is intrinsically 0.57× D+.”

This is `lake env lean <file>` in a fresh process with imports already built: elaboration/kernel checking and process/import overhead, not end-to-end Lake scheduling/code generation, clean Mathlib bootstrap, cached incremental edits or full-gate latency. Every agent iteration does not necessarily re-elaborate every module. Preserve that distinction in the ruling.

**Finding E4c — replay costs similar; export size deterministic; round-2 rank confounded.** M3 seconds = median [min,max], three interleaved repetitions. RSS = maximum over those repetitions, KiB. MB below = decimal 10^6 bytes.

| roots | total export bytes | export seconds (one observation) | leanchecker seconds; max RSS | con-leche seconds; max RSS |
|---|---:|---:|---|---|
| baseline statements | 45,047,166 | 4.40 | 6.84 [6.83,7.00]; 188,896 | 9.15 [9.09,9.38]; 107,932 |
| C S1–S5 | 145,974,391 | 9.71 | 52.44 [50.46,56.04]; 2,059,972 | 60.37 [59.26,62.56]; 2,582,452 |
| D+ S1–S5 | 145,717,133 | 9.94 | 53.73 [53.01,60.07]; 2,059,820 | 63.00 [62.61,63.19]; 2,580,560 |
| V S1–S5 | 160,598,732 | 12.60 | 52.84 [52.43,62.82]; 2,069,932 | 61.70 [61.19,62.88]; 2,577,032 |
| C SegC | 128,666,175 | 9.47 | 84.99 [80.22,99.78]; 2,043,204 | 96.48 [90.13,99.49]; 2,546,656 |
| D+ SegC | 126,858,313 | 11.63 | 105.25 [51.24,116.95]; 2,045,716 | 94.70 [50.69,96.64]; 2,548,836 |

S1–S5 C/D median gaps = 1.29 s LC (2.40% of D) and 2.63 s CL (4.17%). LC ranges overlap substantially. CL is consistently lower for C in these samples, but its worst C and best D differ by only 0.05 s. “Similar practical cost, no decisive replay penalty” fits; exact equality or statistical equivalence does not. No equivalence margin/design or power calculation was specified. V's larger export does not translate monotonically into slower replay, another reason source/export size is not a universal runtime model.

Round-2 D LC climbs 51.24 → 105.25 → 116.95 s and CL 50.69 → 96.64 → 94.70; MAIN reports a concurrent z3 process on the SMT sibling with load up to 18.2. C's first round already occurs after that episode starts. Those ranges and differing exposure can reverse a median/minimum comparison. Do not rank SegC kernel speed from these runs. Acceptance and observed <600 s resource feasibility remain sound; a “quiet” replay estimate does not follow. Exports are pinned but single-shot: timing differences there remain descriptive.

Cumulative export **growth above the common statement baseline**, MB:

| arm | S1 | S1–S2 | S1–S3 | S1–S4 | S1–S5 |
|---|---:|---:|---:|---:|---:|
| C | 81.151487 | 92.177758 | 94.009202 | 94.060097 | 100.927225 |
| D+ | 80.266385 | 90.846685 | 92.579386 | 92.629272 | 100.669967 |
| V | 85.572503 | 107.072335 | 108.346650 | 108.572216 | 115.551566 |

C−D final delta = 257,258 B (0.256% of D's increment; 0.177% of its total closure). S4 marginal growth C/D = 50,895/49,886 B; S5 = 6,867,128/8,040,695 B. This supports sharing on the specific reuse task. S1 contributes about 80 MB and S2–S5 about 20 MB more for C/D; identifying exactly how much of S1 is common stepper/library versus first proof requires a dependency attribution not performed here. Root-union serialization is not the sum of individual roots. SegC has no separate statement-only baseline in this dataset; its total export is not an incremental addition to S1–S5.

**Projection, M6 (non-deciding): full-decoder replay remains unidentifiable from these data.** Formally the planning quantity is `T(reachable union of common proofs + chosen S1–S5 + SegC + SegB + SegD + final composition)`, not instructions × a copy-loop rate or the sum of separate root times. The new roots and their reduction/sharing interactions are unmeasured. Even replaying the two *existing* exports separately yields only a descriptive workload: C median-sum 137.43 s LC / 156.85 s CL; D 158.98 / 157.70, under mismatched load regimes. Those sums are neither final-union estimates nor upper bounds. A numerical full-decoder forecast would need unvalidated linear/additive assumptions; I do not supply one as evidence. The current ~one-minute S1–S5 replay proves useful headroom on this slice, not the final theorem's resource bound. Measure the assembled roots when the implementation provides them; never use M6 to select the engine.

### E5

**Finding E5a — strongest case for C: current artifact readiness + materially lower observed elaboration.** Exact-root/default-kernel eligibility is settled (E1). C is cheaper on every observed full-arm build total, and its advantage survives whole-S5 changed-module accounting (28.28 versus 83.42 s Σ medians, P5), not just root-only factoring. Replay shows no decisive cost penalty. This gives a meaningful practical reason to prefer the available C package for the remaining decoder, even though the frozen line coordinates leave rule 3 inconclusive.

The small batching interface covers all frozen task shapes and the new byte-dependent loop; round 2 changes none of its four `Block*.lean` modules (source-diff rc 0, four-file positive control). `blockEval` repeatedly invokes the existing reference `seq`/uniqueness/access equations, records the access trace, and one soundness theorem transports `Until` (`C/FVA/Proof/Lib/BlockEval.lean:65–100`). `wasm_eval` leaves aggregate footprint + successor obligations (`:107–143`). This is a reusable certificate boundary, not a second trusted execution semantics. Total source is slightly smaller; SegC's continuation/local representation was cheaper. The authoring speed/size observations support local readiness, at lower evidential weight than the replayed artifact and measured elaboration because author × engine is confounded.

**What C cannot show.** No automatic block discovery, fuel selection, invariant synthesis or full decompilation-to-model theorem: the author supplies slices, numerical fuel, branch facts and induction. Both engines use the same underlying stepper; the architectural contrast is chiefly certificate composition + proof representation. The lower round-2 total does not identify batching as its cause (E3). No measurements on another binary/compiler profile, future agent, long decoder tail or memory-writing table path. Smaller proof source does not lower the human-review surface or trusted base; both packages are proof-side (`Contract:3`).

**Finding E5b — strongest case for D+: smaller decoder-shaped source + operational continuity.** S5's marginal source is 27 lines smaller (26 when charging its changed tactic line); `wasm_dstep` builds each unique `seq` step and discharges the footprint, preserving a one-step failure boundary (`D/FVA/Proof/Lib/Direct.lean:132–171`). MAIN's Entry/ErrRet/SegA use `wasm_cstepu`/`wasm_within`; D+ is a direct automation continuation of that style, so familiar numeric/context lemmas and debugging habits plausibly transfer. This is a credible maintenance-policy argument, not measured maintenance superiority. ExtL1B's completed shared proof now removes that immediate obligation from either candidate's remaining burden (E3c), rather than giving D+ an extra experimental win.

**What D+ cannot show.** MAIN's older tactic proofs are not an additional D+ benchmark arm. Both new engines expose the same `Until` interface, so choosing C does not require rewriting those completed cutpoints; `Cut/SegA.segA_of : ExtL1B → SegA` is engine-independent (`:249`). D's one-step control did not prevent 20+ GB authoring failures or expensive S5 joins. Its extra SegC state-preservation source may be a removable representation choice, not an intrinsic tax on direct stepping. No evidence establishes better future-agent usability or a smaller long-run package.

**Finding E5c — shared failure mode: term/state normalization, not untrusted proof search.**

| observation | checked evidence | inference + limit |
|---|---|---|
| C backward-copy kernel recursion | `data/c/build-032.log:5`, `build-034.log:5–10`; symbolic-base revision builds `Backward2` in 16 s (`build-035.log:3–10`). | Concrete modular numerals/normal forms can overwhelm C too. The report's attempted maxRecDepth 20000 is not independently reconstructed from a failed source snapshot. |
| D backward-copy growth | `build-47.log:12,153`: deep recursion, 276.93 s, 20,825,812 KiB (~19.86 GiB); `build-50.log:12–17`: terminated Lean rc 143, 144.32 s, 22,817,616 KiB (~21.76 GiB). `builds.tsv` records runner rc 1 for both. | These are real failed authoring attempts, not final-engine RSS or proof rejection. Abstract-bias helpers subsequently build (`build-49.log:12`, `build-51.log:12`); same conceptual repair as C. Do not attribute the mechanism solely to engine class. |
| Both SegC proofs raise recursion depth | C default-depth `simp` failure (`round2-build-003.log:3–5`), final source depth 4000 (`C/SpikeC/SegC.lean:11`); D default-depth failure (`build-75.log:4–11`), final loop/root depth 2048 (`D/SpikeD/SegCLoop.lean:8`, `SegC.lean:8`). | Finite elaboration needs tuning in both; raising depth is not a kernel bypass. The numeric option values are not a comparative robustness score. |
| D S5 state-update cost persists after repair | Stopped attempts: `build-68.log:5–10`, `build-69.log:5–10`; cached identities retained; final roots 142/162 s (`build-72.log:3`, `build-73.log:19`). C's first green S5 = 30 s (`build-060.log:9`). | M2 confirms a large observed elaboration gap, including all S5 changed modules (E4/P5). The stopped attempts might eventually have finished; neither timeout nor irreducible method failure is established. |

Final observed resource margins and default-kernel acceptance pass for all arms (E1). V is dominated under the actual full rule-3 vectors (E2), not merely unfinished. Recounted `measure/prep-v.log` = 40 `warning:` lines, rc 0 for the counting command; its `--wfail` rejection is gate hygiene, not proof unsoundness or a general refutation of VC generation. C's failed-authoring peak RSS was not measured in the inspected logs; failure-class narratives cannot bound or rank its tail memory risk against D+'s more explicit telemetry.

**Finding E5d — appraisal of MAIN's completed draft.** Provisional C for SegB/SegD is a defensible qualitative choice, **not a compelled empirical winner**. The strongest ground is the observed elaboration advantage across whole-arm and S5 scopes; source/M0 benefits are supplementary, author-confounded and modest in total source. Keeping the existing stepper fallback preserves the common proof interface. “C for later subjects” can be a maintenance default to test, not a demonstrated scaling claim. Reviewed draft = `ruling-draft.md`, SHA256 `1693242b808a4a5a888183286a72b866f9506bde2eeee95c1f747b5c6ff37afa`.

The current draft incorporates the observed-maxima, similar-replay, changed-module timing, ExtL1B-status and S2-versus-S5 failure distinctions. Remaining qualifications:

- **Build effect:** 0.53–0.58 describes two summary ratios under uneven contention, not a confidence interval or the ratio in every run. The *direction* holds in every observed total. This workload informs fresh recompilation of affected proof modules; it is not a measured full-gate or incremental-edit speedup.
- **Kernel comparison:** “similar” is justified; “no measurable kernel difference” is too absolute. Bytes differ deterministically and CL timings favor C slightly; neither a decisive practical advantage nor statistical equivalence is established. The inferred common stepper/library origin of all ~80 MB paid at S1 is not isolated by the export totals alone.
- **Instruction extension:** shared `seq` means neither engine duplicates the ISA interpreter. It does not guarantee a new instruction needs no automation/normalization/uniqueness/footprint lemma or engine adjustment. Current source demonstrates the architectural route, not all future instruction support.
- **Failure asymmetry:** D's recorded >20 GB events were S2; S5's stopped runs were ~2.9 million KiB and long CPU time. C's recorded failure classes do not establish a lower worst-case memory bound. Prospective fuel inference/byte-range automation is a design hypothesis, not measured development cost or guaranteed confinement to the current 129-line file.

Suggested scientific conclusion: **C has the lower observed fresh-elaboration cost among the completed implementations on this decoder. Adopt it provisionally for the remaining cutpoints, retain the existing stepping fallback, and establish readiness anew on future subjects.** The user's maintenance preferences may still favor D+ without contradicting rule 3; evidence does not eliminate that value judgment.

**Knowledge fit, not external performance extrapolation.** The survey's primary excerpts support factoring and compact residual goals, not a C/D winner. liblzma/VST reports “only about 2% ... are forward steps” and an “18-conjunct ... argument, written out 63 times” ([paper §6.2](https://arxiv.org/html/2608.29716v1), `researcher-4.md` R4.6); SymCrypt/Aeneas reports kernel-proved `decompose` transformations and warns it does “not attempt to quantify productivity benefits” while tools/agents evolved ([paper §5,8](https://arxiv.org/html/2609.15648v1), R4.2/R4.5). Those are different semantic/tool boundaries, source-reported rather than replayed here. SegC's plumbing gap and both arms' normal-form failures are consistent with that mechanism hypothesis; they do not independently validate those projects or a universal “invariants dominate” law.

### E6

**Finding E6a — planned decisive check resolved; no added prerequisite for a provisional policy choice.** Phase A prioritized exact-root two-kernel acceptance/resource checks because failure could change eligibility. They now pass for both finalists; C+D final closures cost two exports + 12 replay processes = 716.39 s of recorded process wall time (P4), excluding intervening jobs/baseline/cumulative earlier exports. Both SegC roots also pass. This resolves that doubt rather than leaving readiness assumed. It does not break the frozen C/D line crossing.

**Single optional measurement most likely to change the *primary ground* of the current ruling:** paired fresh-process timings of every unchanged S5-checkpoint added/changed module, on the same host/CPU while its SMT sibling is idle and concurrent load is absent or recorded. Alternate C/D order; one warm-up + three repeats; preserve files, toolchain, flags, imports and resource limits. This tests whether the large build advantage survives genuinely comparable execution conditions. Cost scenario from current Σ medians = `4 × (28.28 + 83.42) = 446.80 s` (~7.4 minutes, 48 module processes), plus scheduling/quiet-slot wait; not a promised duration. No proof authoring or new target is needed. **Not run here; not required before this bounded local choice**, because the observed separation already spans whole-arm and whole-S5 accounting. A small numerical adjustment would not change the practical preference; a reproducible reversal would.

No single timing measurement can identify a causal C-versus-D+ *authoring* advantage. A replicated author×engine×subject design would address that broader claim at proof-campaign cost, with carryover controlled; it is outside the frozen no-round-3 scope (`Contract:62`). Consultants provide judgment, not experimental replication.

**Finding E6b — draft reversal condition is useful but incomplete as an evidence rule.** A same-strength, same-block stepping fallback succeeding where C repeatedly hits a resource obstruction is a good discriminant. Preserve the same input domain, proof obligations, state abstraction and host/limits; otherwise a normal-form repair or load change can masquerade as an engine advantage. Two problematic blocks can justify changing the maintained default, but “more than one block” is a policy threshold, not data-derived necessity; it must not postpone reporting one unfinishable milestone. Coverage stalls, independent-checker rejection/replay-resource failure, and unacceptable proof-size/iteration cost also matter, not only kernel-depth or 12 GiB failures. The user's milestone stop-with-evidence rule still applies.

“Against S5's rate” is only a descriptive reference: SegB/SegD are not S5 scaled by instruction count, source lines or authoring minutes. Compare exact acceptance and observed resources; do not create a new time/LOC gate or declare failure from a point forecast. Local fallback on one block remains consistent with keeping one primary engine.

**Implications / next analyses, ranked by information value.** (1) Proceed to actual SegB/SegD acceptance with frozen `Until`/`Within` interfaces; log new semantic obligations, state adapters, normal-form fixes and resource margins. This is implementation of required coverage, not another competitive spike. (2) If the quantitative speed ratio itself must become a durable general claim, run the optional paired S5 resource check above; otherwise retain the observed-condition wording. (3) Export/replay the assembled full roots when available, then report actual union growth rather than additive/per-instruction projections. (4) Broader method-superiority or future-agent claims require new independent subjects/authors, not more timing repetitions of these same proofs.

Testable cross-method hypothesis: reusable local-state/normal-form adapters reduce more authoring work and heavy proof-term incidents than replacing the stepping backend. SegC's plumbing decomposition + both arms' analogous modular-arithmetic repairs motivate it; neither proves it. The useful next observation is fewer reconstruction obligations/failures on unchanged required cutpoints, with helper investment charged, not a hand-selected reduction in “execution” lines. Minimal review surface and common kernel-checked interfaces preserve the option to change engines later without reopening the user's program specification.

## Probe record

### P1 — frozen line-coordinate sensitivity (text arithmetic; no build)

```sh
awk 'BEGIN{c=511+632+113+26+368;d=505+638+164+34+341;v=553+778+335+119+663;
printf "C_total=%d D_total=%d V_total=%d\n",c,d,v;
printf "C_le_D_both_a=%d D_le_C_both_a=%d V_le_C_both_a=%d V_le_D_both_a=%d\n",(c<=d && 368<=341),(d<=c && 341<=368),(v<=c && 663<=368),(v<=d && 663<=341);
printf "changed_line_accounting_C=%d D=%d D_S5=%d\n",c+1,d+1,342;
printf "sensitivity_total_gap=%d sensitivity_S5_gap=%d\n",(d-5)-(c+5),(368-1)-(341+1)}'
rc=$?; printf 'line_probe_rc=%s\n' "$rc"
```

```text
C_total=1650 D_total=1682 V_total=2448
C_le_D_both_a=0 D_le_C_both_a=0 V_le_C_both_a=0 V_le_D_both_a=0
changed_line_accounting_C=1651 D=1683 D_S5=342
sensitivity_total_gap=22 sensitivity_S5_gap=25
line_probe_rc=0
```

### P2 — raw round-2 accounting + counterfactual partition

```sh
jq -r '[.declarations[] | .codeLines] | add' /home/eturkes/Projects/fva/.scratch/u19c2/spike-c/round2-lines.json
jq -r '.summary | "C total=\(.codeLines) execution=\(.execution) model=\(.model_arithmetic) plumbing=\(.cutpoint_plumbing)"' /home/eturkes/Projects/fva/.scratch/u19c2/spike-c/round2-lines.json
awk -F'\t' '{c[$3]++; if(seen[$1 FS $2]++) duplicate++} END{printf "D total=%d execution=%d model=%d plumbing=%d duplicate_keys=%d\n",NR,c["engine-execution"],c["induction-model"],c["cutpoint-plumbing"],duplicate; for(k in c) printf "D category=%s count=%d\n",k,c[k]}' /home/eturkes/Projects/fva/.scratch/u19c2/spike-d/layers-SegC.tsv
rc=$?; printf 'raw_partition_rc=%s\n' "$rc"
awk 'BEGIN {printf "D_minus_C execution=%d model=%d plumbing=%d total=%d\n",67-73,42-58,178-116,287-247;
printf "C_lower_total_pct=%.2f C_lower_M0_pct=%.2f total_gap_without_module_shell=%d\n",100*(287-247)/287,100*(1930-1366)/1930,(287-23)-(247-12);
printf "C_nonplumbing=%d D_nonplumbing=%d\n",73+58,67+42}'
rc=$?; printf 'sensitivity_rc=%s\n' "$rc"
```

```text
247
C total=247 execution=73 model=58 plumbing=116
D total=287 execution=67 model=42 plumbing=178 duplicate_keys=0
D category=induction-model count=42
D category=engine-execution count=67
D category=cutpoint-plumbing count=178
raw_partition_rc=0
D_minus_C execution=-6 model=-16 plumbing=62 total=40
C_lower_total_pct=13.94 C_lower_M0_pct=29.22 total_gap_without_module_shell=29
C_nonplumbing=131 D_nonplumbing=109
sensitivity_rc=0
```

### P3 — complete data-grid validation + summary cross-check

Read-only Python; every row processed, no sampling. Positive controls alter in-memory copies only.

```sh
python3 -I - /home/eturkes/Projects/fva/.scratch/u19c2/measure <<'PY'
import csv, itertools, sys
from pathlib import Path
p=Path(sys.argv[1])
def rows(n):
    with (p/n).open() as f:return list(csv.DictReader(f,delimiter='\t'))
def validate(rs,fields,expected):
    keys=[tuple(r[k] for k in fields) for r in rs]
    assert len(keys)==len(set(keys)) and set(keys)==expected
    assert all(r['rc']=='0' and float(r['wall_s'])>=0 and int(r['maxrss_kib'])>0 for r in rs)
mods={a:[s.strip()[:-5].replace('/','.') for s in (p/f'modules-{a}.txt').read_text().splitlines()] for a in 'cdv'}
assert {a:len(m) for a,m in mods.items()}=={'c':21,'d':23,'v':37}
expected={(str(k),a,m) for a,ms in mods.items() for m in ms for k in range(4)}
rs=rows('m2.tsv');validate(rs,('run','arm','module'),expected)
print('m2.tsv complete_unique_rows=324 rc_nonzero=0')
bad=[dict(r) for r in rs];bad[0]['rc']='1'
try:validate(bad,('run','arm','module'),expected)
except AssertionError:print('planted_nonzero_rc rejected=1')
else:raise AssertionError('missed bad rc')
bad=[dict(r) for r in rs];bad[-1]=bad[0]
try:validate(bad,('run','arm','module'),expected)
except AssertionError:print('planted_duplicate_missing_row rejected=1')
else:raise AssertionError('missed bad row')
r2mods={'c':['SegC'],'d':['SegC','SegCBase','SegCLoop']}
expected={(str(k),a,f'FVATest.Subjects.Lz4C.Spike{a.upper()}.{m}') for a,ms in r2mods.items() for m in ms for k in range(4)}
validate(rows('r2-m2.tsv'),('run','arm','module'),expected)
print('r2-m2.tsv complete_unique_rows=16 rc_nonzero=0')
for name,exports,tags in [('m3.tsv',['baseline']+[f'{a}-s1-{k}' for a in 'cdv' for k in range(1,6)],['baseline','c-s1-5','d-s1-5','v-s1-5']),('r2.tsv',['c-segC','d-segC'],['c-segC','d-segC'])]:
    expected={(t,'export','1') for t in exports}|set(itertools.product(tags,['leanchecker','con-leche'],['1','2','3']))
    rs=rows(name);validate(rs,('tag','checker','rep'),expected)
    assert all(int(r['bytes'])>0 for r in rs)
    print(name,f'complete_unique_rows={len(rs)} rc_nonzero=0')
PY
rc=$?; printf 'complete_grid_validator_rc=%s\n' "$rc"
python3 -I /home/eturkes/Projects/fva/.scratch/u19c2/measure/summarize.py /home/eturkes/Projects/fva/.scratch/u19c2/measure
rc=$?; printf 'summary_crosscheck_rc=%s\n' "$rc"
```

Control output + selected summary rows (all full summary statistics are tabulated in E4):

```text
m2.tsv complete_unique_rows=324 rc_nonzero=0
planted_nonzero_rc rejected=1
planted_duplicate_missing_row rejected=1
r2-m2.tsv complete_unique_rows=16 rc_nonzero=0
m3.tsv complete_unique_rows=40 rc_nonzero=0
r2.tsv complete_unique_rows=14 rc_nonzero=0
complete_grid_validator_rc=0
c: modules=21 runs/module=[3] Σmedian=120.5s Σmin=118.2s Σrun min–max=120.4–127.8s slowest=S1 17.6s maxRSS=2.71GiB bad=0
d: modules=23 runs/module=[3] Σmedian=226.0s Σmin=205.5s Σrun min–max=206.5–253.5s slowest=S5 64.4s maxRSS=2.99GiB bad=0
v: modules=37 runs/module=[3] Σmedian=622.4s Σmin=526.6s Σrun min–max=528.3–1142.9s slowest=ShortCopies 88.2s maxRSS=3.03GiB bad=0
summary_crosscheck_rc=0
```

Independent inline `csv`/`statistics` recomputation produced E4's unrounded aggregates, observed maxima and per-run vectors; MAIN's reporter cross-check matches. Its docstring calls Σ minima “contention-robust”; that interpretation is rejected in E4b, while its arithmetic is confirmed.

Dataset SHA256s (`sha256sum measure/{m2,m3,r2,r2-m2}.tsv`, absolute paths used):

| file | sha256 |
|---|---|
| m2.tsv | `de4056e34dd709546a6e64e1c07197e5a8b01f65d38b80858e7441f41d849c42` |
| m3.tsv | `ef052f0aeee0fb87c43d835c76d9c3ac9b0663c0d08ef4c8d443a7521fc2b5ed` |
| r2.tsv | `8f25e6b6f45e4c23270914026a96c3556e81a9798078ddd1f718a0f7818c50a7` |
| r2-m2.tsv | `151416b3440fef31eac2c4b33c24dd062c734da8fad508f6511ce8096ced8e16` |

### P4 — frozen runtime-rule and spread sensitivity

```sh
python3 -I - /home/eturkes/Projects/fva/.scratch/u19c2/measure <<'PY'
import csv, statistics as st, sys
from pathlib import Path
from collections import defaultdict
p=Path(sys.argv[1])
def read(n):
    with (p/n).open() as f:return list(csv.DictReader(f,delimiter='\t'))
build=read('m2.tsv'); replay=read('m3.tsv')
m0={'c':[2026,2600,300,57,2048],'d':[2806,2173,537,84,3569],'v':[4156,2221,1432,272,6333]}
cost={}; totals={}
for a in 'cdv':
    groups=defaultdict(list)
    for r in build:
        if r['arm']==a and int(r['run'])>0:groups[r['module']].append(float(r['wall_s']))
    cost[a]=sum(st.median(v) for v in groups.values())
    totals[a]=[sum(float(r['wall_s']) for r in build if r['arm']==a and int(r['run'])==k) for k in (1,2,3)]
for a in 'cd':
    er=[]
    for ck in ['leanchecker','con-leche']:
        mine=[float(r['wall_s']) for r in replay if r['tag']==a+'-s1-5' and r['checker']==ck]
        theirs=[float(r['wall_s']) for r in replay if r['tag']=='v-s1-5' and r['checker']==ck]
        er.append(min(mine)/max(theirs))
    br=max(x/y for x,y in zip(m0[a],m0['v'])); cr=cost[a]/cost['v']
    ok=all(x<=2 for x in [br,cr,*er]); assert ok
    print(a+'_vs_V',f'max_stage_M0_ratio={br:.4f}',f'SumMedian_build_ratio={cr:.4f}',f'worst_observed_total_over_best_V={max(totals[a])/min(totals["v"]):.4f}','replay_min_over_Vmax='+'/'.join(f'{x:.4f}' for x in er),f'all_b_c_e_below_2={ok}')
c5=[float(r['wall_s']) for r in build if r['arm']=='c' and r['module'].endswith('.S5') and int(r['run'])>0]
d5=[float(r['wall_s']) for r in build if r['arm']=='d' and r['module'].endswith('.S5') and int(r['run'])>0]
print('C_vs_D',f'SumMedian_ratio={cost["c"]/cost["d"]:.4f}',f'max_C_total_over_min_D={max(totals["c"])/min(totals["d"]):.4f}',f'S5_median_ratio={st.median(c5)/st.median(d5):.4f}',f'max_C_S5_over_min_D_S5={max(c5)/min(d5):.4f}')
for a in 'cdv':
    vals=[float(r['wall_s']) for r in replay if r['tag']==a+'-s1-5' and r['checker']!='export']
    print(a,'final_closure_replay_all_runs_sum',round(sum(vals),2))
sel=[r for r in replay if r['tag'] in ('c-s1-5','d-s1-5')]
print('C_D_final_exports_plus_12_replays_s',round(sum(float(r['wall_s']) for r in sel),2))
PY
rc=$?; printf 'dominance_probe_rc=%s\n' "$rc"
```

```text
c_vs_V max_stage_M0_ratio=1.1706 SumMedian_build_ratio=0.1936 worst_observed_total_over_best_V=0.2419 replay_min_over_Vmax=0.8032/0.9424 all_b_c_e_below_2=True
d_vs_V max_stage_M0_ratio=0.9784 SumMedian_build_ratio=0.3632 worst_observed_total_over_best_V=0.4798 replay_min_over_Vmax=0.8438/0.9957 all_b_c_e_below_2=True
C_vs_D SumMedian_ratio=0.5332 max_C_total_over_min_D=0.6190 S5_median_ratio=0.2679 max_C_S5_over_min_D_S5=0.2986
c final_closure_replay_all_runs_sum 341.13
d final_closure_replay_all_runs_sum 355.61
v final_closure_replay_all_runs_sum 353.86
C_D_final_exports_plus_12_replays_s 716.39
dominance_probe_rc=0
```

The runtime guard is computed and asserted from the preceding ratios; line-coordinate crossing is checked separately by P1.

### P5 — S5 module-boundary rival check

```sh
python3 -I - /home/eturkes/Projects/fva <<'PY'
from pathlib import Path
import csv, subprocess, statistics as st, sys
root=Path(sys.argv[1]); rows=list(csv.DictReader((root/'.scratch/u19c2/measure/m2.tsv').open(),delimiter='\t'))
for a,lo,hi in [('c','11b97b1','ce5c739'),('d','b9adaf6','43b3653'),('v','a1c9e63','14f50a9')]:
    wt=root/f'.scratch/worktrees/spike-{a}'
    cp=subprocess.run(['git','-C',str(wt),'diff','--name-only','--diff-filter=AM',lo,hi,'--','*.lean'],capture_output=True,text=True,check=True)
    mods=[x[:-5].replace('/','.') for x in cp.stdout.splitlines()]
    groups={m:[float(r['wall_s']) for r in rows if r['arm']==a and r['module']==m and int(r['run'])>0] for m in mods}
    assert all(len(v)==3 for v in groups.values()),groups
    totals=[sum(float(r['wall_s']) for r in rows if r['arm']==a and r['module'] in mods and int(r['run'])==k) for k in (1,2,3)]
    print(a,'S5_changed_modules',len(mods),','.join(m.split('.')[-1] for m in mods))
    print(' sum_medians',round(sum(st.median(v) for v in groups.values()),2),'sum_minima',round(sum(min(v) for v in groups.values()),2),'run_totals',[round(x,2) for x in totals])
PY
rc=$?; printf 'S5_scope_probe_rc=%s\n' "$rc"
```

```text
c S5_changed_modules 5 BlockNumeric,Acceptance,S5,ShortCode,ShortFacts
 sum_medians 28.28 sum_minima 27.8 run_totals [28.04, 29.87, 28.45]
d S5_changed_modules 7 Direct,DirectMemory,S5,S5Code,S5Locals,S5Match,S5Memory
 sum_medians 83.42 sum_minima 80.96 run_totals [81.92, 102.29, 88.75]
v S5_changed_modules 12 CallsTwice,Modular,S5,ShortAttr,ShortCode,ShortCopies,ShortLiteral,ShortMatch,ShortPoints,ShortRooms,ShortSuccess,ShortSupport
 sum_medians 230.39 sum_minima 211.33 run_totals [230.62, 430.91, 212.32]
S5_scope_probe_rc=0
```

These are final-artifact module timings for the files charged at each S5 checkpoint, not new historical authoring measurements or an end-to-end incremental build.

## Scope / check status

- Read: complete contract + arm reports + both prior appraisals + agent-fit survey; complete C/D SegC proof modules and core engine files; complete Seg definitions; ExtL1B + SegA functional bridges; selected ExtDirect invariant/overflow/induction; targeted raw failure/success logs, D3 accounting, acceptance files/logs, both measurement-harness forms, complete TSV data and current ruling grounds. Shared ExtB status checked by declaration/type bytes + commit.
- Passed own text/data checks: frozen Copy/Short hashes for all three arms + Seg hashes for both finalists; raw D3 total/key reconciliation; unchanged-engine diffs (positive controls = four C and five D library files); every expected measurement cell/status, with planted bad-rc and duplicate/missing-row rejection; runtime-rule arithmetic; S5 whole-changed-module sensitivity; summary cross-check; dataset hashes. No new Lean proof or replay run by this appraiser.
- MAIN's archived checks passed: 15 round-1 frozen-root examples + standard axioms; both SegC examples + standard axioms; every recorded export/default-kernel replay and measured module process rc 0. V's `--wfail` acceptance attempt failed on 40 linter warnings; its ordinary acceptance passed. Scope remains the frozen roots, not whole-decoder `fva trust`.
- Coverage limits: historical logs queried at named diagnostic/elapsed/rc anchors; failed source revisions not reconstructed. M0 timestamps/tool counts not audited against full transcripts; exact model/backend/effort, per-process host telemetry and runtime binary/canary manifests not independently audited. Host-history facts supplied by MAIN are labelled. Source-line partitions remain author-labelled; reuse-list denominators differ. Full data-grid/statistics counts are unsampled. External primary pages not reopened; knowledge excerpts come from the supplied survey, with its scope limits.
- Not run: any build, Lean invocation, independent replay, `fva trust`, gate, live Wasm execution, fresh browser research, quiet paired-S5 repeat or new proof experiment. No source/contract/gate edit, commit, peer dispatch or write outside this validator input. Notify-set edits = none.
- Final validator passed: `rows=6 headings=6 complete_cells=30 phase_A_markers=1 final_markers=1 probe_sections=5`, rc 0; seed-cell scan = 0, rc 1 (expected no match), positive control expected/observed 1, rc 0. Stale pending-claim scan = no matches, rc 1. Verdicts = E1/E2/E6 supported; E3/E4/E5 partly, with limits/rivals stated above.

scientist-3-PHASE-A

scientist-3-DONE-1
