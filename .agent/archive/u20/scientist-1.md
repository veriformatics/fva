# scientist-1 — U20 spike-check appraisal

Validator: `grep -c "| unknown |"` on this file → 1 (this preamble alone). Table cells are resolved.

**Ruling: revise the protocol before launching; retain D+, V, C and S1–S5 as a useful bounded engineering comparison.** The present check can compare completed implementations on copy composition and one conditioned decoder path. It cannot establish an engine-class scaling winner, and its runtime/growth and marginal-cost rules are not yet operational enough to grade fairly. No counterexample to a frozen statement was established in this appraisal. The recommendations below change the measurement/interpretation contract, not the reviewed Wasm semantics or checkpoint-1 proofs.

| id | claim (U20 design element) | verdict (supported / overstated / unsupported / open) | reasoning + rivals | fix or next test |
|---|---|---|---|---|
| C1 | S1–S5 form an informative slice for choosing the decoder's stepping engine | supported | Meaningful I4/I5 vertical slice: two distinct overlap contracts, total calls under arbitrary caller contexts, unbounded copy loops, reuse at changed locals/exits, and one 19-local decoder path with four calls. P1 confirms 129/550 func-2 static nodes and 6/11 call sites. S5 fixes all seven branch directions; no unknown branch split/join or main-invariant restoration is tested. | Keep the slice; label its discrimination domain. Before a general scaling ruling, require a small two-exit/join + prefix-relation adapter, or explicitly keep the choice provisional until the first such decoder unit. C1, C6. |
| C2 | Fresh parallel authors remove order/carryover; residual author variation is acceptable at this size | overstated | Removes the documented *new-arm copying/order mechanism* if blinding holds. One author trajectory per engine leaves author×engine fully confounded; common model lane is not replication. D+ also inherits the most mature project machinery. Parallel waits/resource contention, prompts, model/backend and checker drift need controls. | Keep n=1 for a project-local implementation choice, not causal engine superiority. Pin the run manifest, equalize starting assets/resources, record censoring; replicate a decisive close contest only if a broader superiority claim is needed. C2. |
| C3 | M0–M6 measure marginal cost, scaling, elaboration/replay resources and coverage | overstated | Most useful observables are present, but per-root export totals do not isolate growth; prebuilt-import module timing can omit new infrastructure; S2/S1 changes semantics as well as size; statement-specific LOC can move into infrastructure. M3 has one observation but is used as a paired-run discriminator. | Add cumulative distinct-root closure snapshots + baseline, all-new-module build cost, per-stage added/changed declarations, raw resource manifest, and repeated M3 if timing ranks. Rename ratios as task-specific transfer observations, not scaling estimates. C3, P3. |
| C4 | The eligibility/½-lines/2×-time/secondary rule is decisive and resists false winners | unsupported | Not executable without interpretation: M2/M3 are vectors, aggregation/checker conflicts and three-arm outcomes unspecified; M3 has no paired repeats. Primary can prefer the same work after reclassification, or a completed arm with 100× replay cost; P3 constructs both. A single eligible arm establishes bounded readiness, not intrinsic method superiority. | Freeze an explicit partial-order/policy rule with total incremental cost visible, practical resource bounds, no regression hidden by LOC, and an inconclusive outcome. Fix M3 repeats or remove its timing from selection. C4. |
| C5 | Drop a separate R arm at S1–S5; use a decoder-level model above the stepping engines | supported | Composable-layer interpretation fits the inspected research; S1/S2 already specify functional memory transformations. A separate copy-loop model would mainly test another representation choice. This is a justified architecture hypothesis, **not** an empirical rejection of refinement or proof that a whole-decoder model is cheaper. | State that the spike compares low-level engines conditional on a shared model/cutpoint interface. Keep Model proof-side, prove Model→format separately, and do not make R1 depend on completing all R2/R3 model work. C5. |
| C6 | Differential Model tests + model-level one-sequence invariant adequately test the I7 semantic risk independently of instruction stepping | overstated | Good separation of parsing/format reasoning from machine execution. It does not test the concrete-prefix/scratch relation or invariant reconstruction at a join. I7 is prose, not yet a fixed theorem family; an easy shortcut-only result could satisfy a loose reading. Test corpus compares outcomes, not access footprints/termination, and samples one placement. | Freeze soundness/completeness domains, margins, zero-offset semantics and progress/fuel obligations. Add a kernel-checked exact-copy→valid-prefix adapter using S5's poststate; gate the method ruling on the specified I7 result, not differential agreement alone. C6, P2. |
| C7 | Eight hours / context headroom is adequate and fair across arms | open | No matched effort evidence establishes adequacy. Equal elapsed time is a reasonable bounded continuation budget, but a variable context stop and unequal host waits are not equal opportunity. C/V incur fresh bridge costs; excluding these from the primary metric while using them to censor eligibility mixes objectives. | Define one operational budget, pause policy, context-resume policy and checkpoints; record initial context, model use, compute/wait time and setup separately. Report exhaustion as right-censoring, never method failure. C7. |
| C8 | I1–I11 + R1–R3 ledger operationalizes theorem coverage | supported | Domains, paths and named conditions are the right units. Static nodes and “5/5” alone are not semantic coverage; I4/I5 contain subcases and a model theorem is not a byte-linked theorem. A proved implication conditional on a missing invariant remains conditional. | Make the ledger an actual acceptance artifact with theorem roots/types, dependency status, semantic layer, path/subcase, axioms + per-checker status; label union counts as supplementary, never percentages of correctness. C8. |
| C9 | The present design has no additional launch-critical omissions | unsupported | Additional omissions: porous mechanism boundaries; no precise frozen measurement manifest; statement/body closure and false-input checks underspecified; differential evidence overstated if treated as independent trials; marginal score omits shared-work chronology. | Apply C9a–C9e before launch/selection at the boundaries stated below. |
| C9a | D+, V, C are sufficiently distinct treatments under the current allowed-work rules | open | D+ may add cached block lemmas and arbitrary automation; C may choose only straight-line summaries or full structured control; V needs a sound WP bridge and may fall back to D+. Successful arms could converge on the same mechanism with different names. | Freeze the primary mechanism + allowed fallback for each arm. Record which mechanism actually discharges every statement. Hybrids are useful outcomes, not clean engine comparisons. |
| C9b | Frozen statements and standard axioms alone make the acceptance harness ready | open | Copy/Short hashes match. Source inspection supports stated paths; P1 confirms the WAT matches the shipped bytes. Existing concrete sanity file exercises copies only, not S3–S5 cutpoints/footprints. `#print axioms` does not certify root identity or nonvacuity. | Preflight exact S1–S5 root-type checks, baseline export/replay, and a concrete nontrivial S3/S4/S5 trace/cutpoint check with a planted wrong exit/byte/range. Pin Short.lean and all shared semantic/proof inputs, not just Copy.lean. |
| C9c | The differential total and mutant score support broad semantic validation | overstated | P2: 117,808 rows but 103,070 distinct recorded input/capacity pairs; cases4 has 576 rows/240 pairs, because its `pre`/`head` never enter `blk`. All generators fix source below destination. Twelve mutation edits are listed; per-mutant command/rc records were not located in the supplied evidence. | Report observations, logical uniqueness and case families separately; repair the inert prefix sweep; test both address orders, boundaries and varied initialized destination bytes. Archive mutant command/source hash/rc/kill case; use held-out tests after tuning. |
| C9d | End-state infrastructure/specific/generated LOC categories identify marginal reusable effort | unsupported | A helper added while proving S4 is part of S4's marginal cost even if generic. Final declaration categories cannot reconstruct when/why it was built; source line layout and manual/generated classification are manipulable. P3 gives a classification-only winner flip. | Freeze checkpoints after every statement; count all new/changed handwritten code and generator code by stage as well as final role. M1 remains source size, not effort; M0 and total accepted-delivery cost remain separate. |
| C9e | Finishing the spike closes the highest-value architecture uncertainty | overstated | Stepping throughput is only one uncertainty. The closest decoder evidence concentrates source bulk in repeated invariant reconstruction, not steps. The first target-wide R1 proof and the concrete→format seam remain decisive; this spike must not become a three-engine infrastructure project detached from them. | Use the common Until/Within/call-contract boundary to keep engine replacement possible. Next discriminating unit = one joined decoder path with a small reusable state/prefix invariant, not more copy-only timing repetitions. |

## Scope, evidence pins, and limits

Root = `/home/eturkes/Projects/fva/`; base commit from the brief = `e5de229`. Read the current U20 contract, Copy/Short/Model, U19 contract and E1 appraisal/results, all four U19c2 research reports, func-2 AST paths, complete func-2/3/4 WAT, differential generators/checker/mutation list, copy sanity source, Context/Until/codeLines definitions, and the initial ModelProof extension lemmas. MAIN is still changing ModelProof; this report does not grade its eventual completion. The current Phase request explicitly asks first-use/reuse, export/replay **growth**, theorem coverage, and I7 alongside I4.

Pinned appraisal inputs:

| input | sha256 |
|---|---|
| `docs/contracts/U20-proof-scaling.md` | `1a3558d470f9f1bcdb2735b7444c6ccc0e068b96f8ce93ed4c6278d53f53817f` |
| `FVATest/Subjects/Lz4C/Copy.lean` | `5caf05ac56598440e5b7ee1f58db72c03f41badb7a3ea6342713abb622d57461` |
| `FVATest/Subjects/Lz4C/Short.lean` | `b208722b3ce66f68abd312b126def79e64ea9c8c86bb9ec1c3fda6cce9abe83d` |
| `FVATest/Subjects/Lz4C/Model.lean` | `b30b0bb9f7fae025d791645382d80b780e4ec75aa0f5ba193a3db0b17e6e9946` |
| `.scratch/u19c2/lz4-c.wat` | `009da55f09edb6afa1dbec3598175739fd9b33c6c8ae584f3b28bebe63678a72` |
| subject `lz4-c.wasm` (both locations) | `8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6` |
| supplied `diff/check-native` | `f36fb44910258909d72c382493e2f283d9e3f8438102a035245c638cd972232a` |

Checks actually run: shipped-byte WAT reprint + byte comparison; complete static census of funcs 2–4 and the selected path spans; all five TSV row/uniqueness/outcome counts; native checker on **cases4 only** (576 rows); Model/backup byte equality; synthetic selection-rule sensitivity; seeded-table positive control. No `lake build`, Lean theorem check, gate, fresh proof export, independent kernel replay, full differential rerun, mutant rerun, or fresh web-source retrieval. Built-in LSP was tried on Model.lean: no `.lean` server configured. Research knowledge below uses the reports' pinned primary-source excerpts, not an independent replay of those projects. No outside teammate launched. Writes confined to this report and `.scratch/u19c2/scientist-1/`.

## C1 — useful workload, deliberately narrower than whole-decoder scaling

**Assumptions + fit.** An engine that can prove general total copy calls, compose them through loops, and handle a long local/label-heavy path is more plausible for this decoder than one demonstrated only on U19's read-only extension loop. That assumption fits I4/I5 and some I9. The S1/S2 models correctly separate sequential forward copying from snapshot-preserving movement; they require every execution to reach the exit with an interior access predicate, not merely an extensional final result. Contexts remain arbitrary where appropriate. S3/S4 exercise reusable call contracts under concrete nested labels and different local indices/exits.

**Probe P1.** S3 has 17 static nodes, S4 18, and S5's forced path 94, including structural block/loop nodes. Their union is 129 distinct func-2 nodes and 6 call sites. S5's seven branch opcodes have fixed outcomes under its hypotheses; two short fallback tails are not executed. S1/S2 cover the complete 93-/191-node helper bodies. This is substantial **path/contract** diversity, not five independent problem draws. Do not call S5 coverage of the entire main loop merely because it starts and ends at its header.

The paired S3/S4 pattern is a useful positive transfer control: if reuse is poor even when the body changes only local roles and its final branch, that is diagnostic. Conversely, near-zero S4 cost shows local template reuse, not generalization to error paths, unknown joins, offset tables, malformed inputs, or the one-sequence invariant. S2 is not “S1 at twice the size”: direction selection, backward order, snapshot semantics and modular subtraction change the proof problem.

S1/S2 quantify all bounded addresses below 2^32; the target claim uses buffers in `[131072, 2097152]`. Their broader contract may buy generic library reuse but can consume time on arithmetic not necessary for this artifact. Keep it if intended; record that trade-off before launch rather than narrowing it after one arm struggles.

**Knowledge fit.** The surveys support callee summaries plus explicit invariant work, not a per-instruction cost model. s2n's cited call-in-loop proofs use `ENSURES_WHILE_DOWN_TAC` and `LOCAL_AMONTMUL_TAC`; researcher-1 R1.3 provides pinned source/excerpts. The closest decoder paper says “only about 2% of the lines ... are forward steps” and describes an “18-conjunct ... argument, written out 63 times” ([liblzma §6.2](https://arxiv.org/html/2608.29716v1#S6), researcher-2 R2.4 / researcher-4 R4.6). This is source-text evidence from transformed C/Rocq, not an FVA time prediction, but it directly motivates testing invariant restoration at a join.

**Separating observation.** After fixed copy infrastructure, prove a small pair of real decoder paths that reach a common abstract-prefix/cutpoint relation. Record new semantic facts and state-restoration work separately from machine plumbing. If that is deferred, the verdict must remain “best observed copy/path implementation under this budget,” with a reopening trigger at the first such join.

## C2 — blinding removes one confound, not author variation

Checkpoint 1 explicitly copied the first route's stepping scripts into the second, and reversed order for the optimizer perturbation. Fresh parallel contexts with no cross-arm reads remove that particular within-session carryover path. Shared preexisting D/R proofs remain common starting assets; learning from them is allowed and must be named, not called absent carryover in a universal sense.

With one author trajectory per engine, observed cost = engine + trajectory decisions + their interaction + execution conditions. None can be separated statistically. Three timing repeats on the resulting artifact replicate **runtime**, not proof engineering. S1–S5 are correlated stages of one development, not five engine replicates. No meaningful population success probability, confidence interval on authoring advantage, or power claim follows. A 2× empirical gap is a practical decision margin, not a calibrated false-winner rate.

This is acceptable for choosing among **actual available implementations for this project**, provided scope remains that narrow. D+'s existing library advantage is then a real sunk asset, not a flaw to erase. It prevents a claim about equal-from-scratch method economics. Consultants add judgment, not experimental replication.

Before launch, pin: actual model/backend identity where available; effort, context limit/initial occupancy; complete arm prompt + read set; tool availability and versions; baseline commit and source hashes; allowed existing libraries; CPU/memory limits; start/stop and suspension records; exactly the same theorem/checker harness. Give each arm the same research material and mathematical helper definitions. Avoid route-specific hints delivered after observing progress; if a correction affects the contract, stop and restart/rebase all arms against one recorded amendment.

Parallel authoring should use distinct CPU sets/private build stores and sufficient RAM, with contention recorded. Otherwise one infrastructure-heavy arm can slow another's elapsed M0. Post-harvest balanced timings are a good control; pin exporter and checker processes too, not just Lean elaboration. Same grader/checker binaries and invocation/canary set across arms prevent harness drift.

## C3 — make the requested costs observable

### M0: elapsed construction is not total delivery or active effort

Keep contiguous start→first theorem build, failed attempts and waits. Also record: infrastructure/setup before S1; later repairs to earlier statements; the end of accepted export/replay; elapsed time to the entire accepted suite. A first successful build can precede discovery of a root/export issue. Tool-call count is descriptive: one call can launch a long compile or generate thousands of lines. Model token/turn usage and time waiting for capacity help explain a context/elapsed cap; they do not replace the project's preferred wall-time outcome.

### M1/M4: roles and marginal increments are different axes

`FVA.Trust.codeLines` (`FVA/Trust/Collect.lean:347`) counts physical noncomment code lines. It is a reproducible source-size metric, not proof complexity, effort or readability. Preserve common formatting; store declaration classifications with reviewer-rulable criteria. Count generator code even when generated certificates are reported separately. Identify subject-specific helper facts hidden in a generic-looking library module.

Record checkpoint diffs after S1, S2, S3, S4, S5: every new/changed handwritten declaration, its role, its consumers, and code lines. A generic lemma first added for S4 belongs to S4's observed incremental work. Final-role totals remain useful, but cannot stand in for that chronology. Freeze the reusable package before the S4 transfer; if it needs revision, report the revision rather than classifying it away.

S4/S3 = local-pattern transfer ratio, with denominator uncertainty and zero-cost cases reported directly. S2/S1 = two different helper contracts, **not** an estimate of a scaling exponent. Neither divided by 191/93 removes changes in branches, copy direction, invariant and arithmetic. Source final LOC also omits discarded failed approaches; M0 captures that history only imperfectly.

### M2: incremental build and newly introduced library cost

Three fresh-process runs after warm-up, prebuilt **common** dependencies, balanced order and one host are reasonable descriptive runtime checks. An arm can put expensive proofs into its imported library; timing its wrapper with those imports prebuilt hides that work. Therefore also time rebuilding the complete set of **new arm modules**, retaining the common base cache. Report module-by-module and total results; an import-only baseline is descriptive, not proof-only time obtained by naive median subtraction. Pin CPU affinity, process/thread count, limits, host load and RSS units (GNU `%M` = KiB).

### M3: root closures, shared closure and actual growth

Export/replay each root for acceptance. For the user's growth request, also export cumulative root sets `{S1}`, `{S1,S2}`, …, `{S1,…,S5}` with declaration sharing counted once, plus the fixed statement/common-import baseline. Keep a sorted root/dependency manifest, total serialized bytes, distinct declarations, export cost and each checker's time/RSS/status. This shows whether reuse adds a small delta or duplicates large proof payloads. Separate final-state cumulative closures from historical checkpoint closures; a later infrastructure refactor can alter the earlier root's cost.

Do not sum separate root exports to estimate deployment size: their shared imports repeat. Do not subtract an independently timed baseline and call the remainder an isolated proof-check time; checker initialization/reduction costs need not be additive. Root-union bytes/declaration deltas can be descriptive without that causal assumption.

If replay timing ranks engines, use a warm-up and at least three interleaved fresh-process repeats on fixed exports, keep all observations, and apply the same range rule as M2. One observation per root supports acceptance and observed cost only. Archive rc immediately; distinguish reject, timeout, process crash and setup failure. The U19 con-leche 92.96-second single observation already demonstrates why a one-shot outlier/ranking claim is unsafe.

### M5/M6

Axiom closure and root acceptance are essential, but use exact frozen root types and the C8 ledger. Static nodes exclude dynamic loop iteration counts and do not measure invariant complexity. Report per-node figures only descriptively as the contract already promises. Do not silently count the body of a called helper at every call site or count all paths inside a conditional S5 lemma.

## C4 — selection needs a runnable decision procedure

The current language leaves decisions to the harvest:

- Which M2 aggregate: each statement, all-new-module total, median wall, maximum RSS, or a vector?
- Which M3 coordinate/checker wins when leanchecker and con-leche disagree on relative speed?
- Does M3 break an M2 tie, or can it veto a primary LOC winner?
- With three arms, is a winner required to dominate *both* others, or is beating one sufficient?
- Does the single-eligible rule still apply when another arm is infrastructure-blocked rather than proof-incomplete?
- How are a primary winner and the later qualitative/infrastructure policy reconciled?

P3 is a logical sensitivity analysis, **not measured engine data**. It shows that reclassifying 60 of 100 lines as generic can turn equal total source into a ½-lines winner; an arm with 40 marginal lines and 10,000 infrastructure lines can beat one with 100 + 20; a 100× replay regression can coexist with primary dominance if both finish. These are genuine permitted outcomes of the written rule. They do not prove any arm will game it; they show the chosen metric does not identify the stated lifecycle objective by itself.

Recommended rule, to freeze before execution:

1. **Acceptance first:** exact S1–S5 types, unchanged inputs, allowed axioms, both default checkers; preserve incomplete/blocked outcomes separately. Eligible means completed under recorded conditions.
2. **Report a cost vector:** total incremental authoring-to-acceptance; S4/held-out transfer increment including new infrastructure; total handwritten/generator source; final cumulative export/replay resources. Roles and statement-specific LOC explain the vector, rather than hiding coordinates.
3. **Only call a clear observed preference when it survives the declared sensitivity:** all-new-code versus role partition, shared-closure versus per-root reporting, and every checker's practical resource limits. Pick which trade-offs the project actually values *now*; arbitrary ½/2× thresholds are policy and should be labelled that way. A Pareto trade-off stays inconclusive.
4. **Runtime rank:** a coordinate gets a ≥2× label only on repeated matched observations satisfying the range rule. No-repeat M3 remains descriptive and cannot break a tie.
5. **Selection:** choose a nondominated completed implementation provisionally, with the I7/branch-join acceptance trigger. If only one is completed, say “the only completed candidate under this budget”; do not infer the uncompleted engine could never be preferable. Preserve failure artifacts, not just winner metrics.

No statistical p-value is needed for this engineering spike. Pretending that arbitrary ratios eliminate trajectory bias would be worse than an honest bounded policy choice.

## C5 — shared refinement layer is reasonable, not empirically proven best

The sources give compatible decompositions: concrete machine/callee effects, representation/cutpoint relation, and abstract algorithm correctness. Researcher-2 R2.1 quotes Rupicola's “instantiating the state representation predicate ... partway through iteration” ([PLDI22](https://adam.chlipala.net/papers/RupicolaPLDI22/RupicolaPLDI22.pdf)); Lean-zip relates a fixed buffer's logical prefix to growing output. Researcher-3 distinguishes proof-producing block simplification, verified reflection and full decompilation; they are different investments. Researcher-1's LNSym source already caches generated block lemmas inside a direct symbolic-execution workflow. The layers genuinely compose.

At the copy level, S1's `fwdCopy` and S2's `move` already provide mathematical models. Adding an explicit loop-counter model can test representation choices, but it is not the most useful independent axis for this narrow experiment. Therefore dropping a separately named R arm is defensible **conditional on** treating high-level refinement as an architecture hypothesis and preserving a direct fallback for local proofs. U19's inconclusive result did not eliminate R.

The report's phrase that large proofs' “bulk is invariant reconstruction, not instruction stepping” generalizes one particularly relevant decoder observation too far. Say that this is an observed bottleneck in liblzma and a plausible FVA risk. Other surveyed arithmetic kernels have different dominant costs. No controlled cross-method evidence or FVA break-even has been found.

Keep the model outside the review/import closure; separately prove it meets `Lz4.Valid`/`ParsesAny` obligations, then connect exact machine segments to its prefix view. Model agreement with a buggy binary is not independent format correctness. The model's convenience should not make the earlier whole-domain R1 milestone wait for every functional R2/R3 lemma: safety/progress invariants can be assembled before the complete format proof.

## C6 — I7 needs a fixed theorem and the concrete-prefix seam

**What the proposed split does test:** the arithmetic/canonical parsing logic, extension encoding, accepted-sequence characterization and valid-input margins can be proved without expanding Wasm instructions. This is precisely useful independent semantic work. The existing `Model.ext_sound`/`ext_complete` source, read while MAIN was developing ModelProof, moves in that direction; this report does not certify its final build or the eventual one-sequence result.

**What it does not test yet:** S5's poststate is an exact concrete memory transformer with speculative 16/18-byte writes; `Model.step` returns only the decoded prefix. The relation must prove that old valid bytes and the logically new bytes agree while scratch-tail bytes may differ, input remains unchanged, offsets refer to the right updated output, and the next header retains the state invariant. A model theorem plus a separately proved exact-state S5 does not automatically supply that adapter. The hardest residual may be here rather than in stepping.

Freeze I7 before it is used as evidence:

- State the valid-entry relation: input suffix at `i`, output prefix, capacity, represented pointers, and facts about prior parsed sequences. Bound the model domain to U19's fixed memory geometry rather than silently claiming arbitrary Naturals.
- **Soundness:** every accepted continuation consumes the bytes of an actual `Seq` under `ParsesAny` and appends exactly the `Lz4.copy` result; an accepted final-literal step consumes the entire remaining suffix. Explicitly include offset 0's chosen semantics.
- **Completeness:** a valid next sequence plus the appropriate remaining-valid-suffix/end-condition/room hypotheses passes the decoder-specific tests. “A valid sequence passes every check” without suffix/position/margin conditions is insufficient: the decoder's guard inspects bytes after it.
- **Progress:** continuation strictly advances the input position and preserves bounds; show adequate loop/extension fuel separately. A total fuelled Lean function may return failure because fuel runs out; that alone is not guest termination or a model completeness proof.
- **Concrete adapter:** under a shared memory-prefix relation, project S5's `fwdCopy (fwdCopy ...)` result to the corresponding `Model.step` prefix, preserving the relation for the next head. This can be proved independently of stepping, then instantiated by every arm. Record its common cost; do not credit it to one engine.
- Include at least one margin/general/zero-offset case in the fixed I7 theorem family, or name exactly which such risk remains open. A shortcut-only result cannot stand for the whole I7 inventory.

P2's differential result is useful fault detection, not proof: logical-case duplicates, one placement, small lengths, stateful reuse in two generators, and an outcome-only comparator limit it. `none` merges all negative results; that is aligned with R1–R3's current return specification (no exact error code claim), but tests neither the negative-return footprint nor all-prefix safety. Padding initialized to `0xAA` in gen.py is not an independent arbitrary-initial-memory proof; gen2/gen4 reuse previous memory without recording it. Boundary/mutation tests should target these gaps, not merely raise the row total.

## C7 — budget and censoring

Eight hours is a project policy, not a data-supported adequacy claim. Prior art ranges from small helper proofs to substantial framework work; none supplies a matched forecast for a fresh Lean 4.35 WP/reflection bridge with these exact axioms/checkers. A C or V arm that spends the budget creating sound reusable infrastructure and stops before S5 is censored, not falsified. D+'s head start is relevant if the objective is “what can we ship next from this repo”; it is confounding if the claim becomes “which method scales best from equal maturity.” State the former objective.

The phrase “or its context headroom” is not operational: threshold, initial occupancy, compaction/resume rules and successor policy are unspecified. It can selectively end a verbose/debug-heavy trajectory before eight hours. Either permit continuation from a durable checkpoint under the same aggregate budget (same policy for every arm), or declare a fixed token/context cap as a second budget and measure resource exhaustion explicitly. Record the effective budget received, not just nominal cap.

Use stage checkpoints and a small early feasibility milestone (e.g. one total/footprint-preserving primitive or call-rule bridge), but do not eliminate an arm opportunistically because another advances faster. Predeclare any stop criterion and retain partial soundness code/last obligation. Common setup/model work stays outside all arm budgets and is reported separately; engine-specific setup remains inside. Suspend elapsed authoring time consistently for infrastructure outages/user scheduling, while keeping full calendar latency as a separate observation.

## C8 — coverage should describe proofs, not progress impressions

Required ledger columns:

`obligation/subcase | exact theorem root + type | domain/extra hypotheses | concrete path/cutpoint | semantic layer | proved dependencies / open dependencies | allowed-axiom closure | checker statuses | status`.

Use `proved` only for the named domain/path and closed dependencies. `proved conditional` is a meaningful theorem but not completion of its missing assumptions. `model-only`, `machine-segment`, `whole-call` and `byte-linked final claim` are distinct layers. Root type checks prevent a weak helper with an impressive name from becoming “R1 proved.”

Examples of honest scope after successful S1–S5:

- I4: both complete helper contracts; caller compositions at six selected memcpy call sites. Not every func-2 call site.
- I5: two of three wildcopy loops; near-end copy plus tail composition still open.
- I9: selected wildcopy and shortcut interior footprints under stated bounds, not whole-domain R1.
- I7/I8: whatever exact model/prefix lemmas were actually proved; full main-loop simulation and reverse accepted-input reasoning remain separate.
- I1/I6/I10/I11 and final R1–R3: retain explicit open subcases until their target theorems close.

Static-node counts are a useful index for where proofs attach, never a percentage of correctness. A loop's syntactic coverage is not coverage of its invariant, exit completeness, termination or all legal inputs. Preserve the predecessor U19 inventory's narrower statuses rather than promoting an analogous pattern to a proved target transfer.

## C9a–C9e — launch contract and remaining blind spots

### C9a: mechanism boundaries

Suggested minimal distinction:

- D+: proof-producing tactic composition of existing small-step/Until rules; per-block cached theorems permitted, no new symbolic interpreter as its primary execution path.
- V: instantiate `Std.WP`/`vcgen`; prove the actual total/footprint bridge to Until; registered call/loop contracts drive statement proofs. Partial-correctness WP alone is ineligible.
- C: a reusable proved block/symbolic evaluator whose soundness theorem supplies the execution certificate; explicit scope of supported control and handling of open symbolic state. It must not merely rename the D+ tactic.

Shared arithmetic/memory semantics and callee contracts are allowed everywhere. Log fallback stepping per statement and any hybridization. A hybrid that wins is valuable engineering evidence, but the result then compares implementations rather than the original pure mechanisms. Allowing C to attempt a full interpreter while D+ only batches straight-line rules is an uncontrolled scope choice unless that investment is part of the declared objective.

Knowledge fit: Lean 4.35's release says `vcgen` can verify “deeply embedded languages ... x64 assembler or WebAssembly” ([release](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/), researcher-1 R1.7). Its WP class supplies a monotone transformer, not FVA termination/access soundness; the cited IMP loop example lacks a decreasing measure. Picinae's evaluator stops “early ... conditional or loop” to avoid fully expanding every branch ([pinned source](https://github.com/CharlesAverill/Picinae/blob/a87fc67dd1bafd4eccb35812f6459f51e4d79e3b/Picinae_finterp.v#L474-L483), researcher-3 R3.6). These justify the candidates and explicit stop/soundness boundaries, not a predicted winner.

### C9b: preflight and frozen manifests

Pin **all** common inputs: Copy, Short, Code, Ext, Instance, Lifted, existing libraries, toolchain/Mathlib, model interface if consumed, commands, checker binaries/canaries and run limits. U20 currently still says “S1–S4” in tiers/allowed categories despite adding S5. The forbidden-edit list explicitly names Copy but not Short or the forthcoming I7 statements; all grader statements must be equally frozen. A declared frozen section helps, but the arm brief and acceptance diff check should enforce the complete set.

Require `example : MemcpyS1 := Arm.s1` etc. (or equivalent exported type equality), then axiom/root-closure checks and both checkers. Audit emitted assumptions and transitive imports; standard axioms do not make a vacuous precondition meaningful. An import/wrapper build is not the accepted proof deliverable.

The existing CopyRun source has concrete forward/backward overlap examples and a memcpy≠move control; that is appropriate preflight for S1/S2, not a full-domain proof. S3/S4/S5 also need at least one nontrivial concrete witness for the expected cutpoint/locals/bytes and one deliberately wrong prediction that fails. A misindexed continuation or missing boundary premise should be diagnosed as a common statement/harness defect before consuming three budgets. Such samples cannot establish universal truth, so preserve failure classification for an ill-posed statement discovered later; do not treat that as an engine loss.

### C9c: differential validation is useful but narrower than the headline count

See P2 for complete recomputation. All 117,808 records have three fields in the inspected files; observed outcomes agree for repeated recorded `(input, cap)` pairs. Some repetitions may have different **unrecorded** memory states because gen2/gen4 reuse one instance; therefore 103,070 is distinct logical input/capacity pairs, not an independent-trial count or complete concrete-state deduplication. The repeated `pre` loop in gen4 contributes no prefix because `head` is unused; its first branch family is repeated eight times.

No mutation command/output ledger was present in the named diff files; `mutants.txt` records 12 edit pairs, not their outcomes. The reported 12/12 is therefore **unconfirmed by this appraisal**, not contradicted. A test suite adapted to kill particular mutants is valuable development coverage; it is not a held-out estimate of general bug detection. Record which cases killed which mutants and whether they were added after seeing a survivor, then add orthogonal/held-out memory-layout and prefix cases.

### C9d: marginal economics

S1–S3 build the package; S4 is a transfer observation; S5 is a new workload type. Treat that chronology as data. An engine's generically named lemma is not free because it could be used again. Record all new code and time at each stage, retained/deleted experiments, and future consumers actually demonstrated. Any amortization past those uses is a scenario, not observed reuse.

A modest sensitivity table can ask whether the winner survives counting all engine infrastructure now versus charging only its measured stage increment. If the winner flips, this is the project decision—short horizon versus expected reuse—not a measurement error to hide with LOC categories. Never infer break-even from 550 instructions times a copy-loop line ratio.

### C9e: highest-value uncertainty and reversibility

Common proof judgments make the engine choice less irreversible than the prose framing suggests. Keep theorem interfaces in `Until`/`Within`, exact helper contracts and a compact representation relation; D+, V and C certificates can compose. A failed engine optimization then need not invalidate established semantic lemmas or rewrite the human-facing spec. That is a stronger risk-control measure than overinterpreting one three-arm race.

Bold, testable hypotheses for the next unit:

1. A reusable **state/prefix invariant restoration lemma** reduces marginal proof work more than replacing the stepping backend. Distinguish by logging restoration versus execution obligations at a shared join.
2. Independent replay growth is driven more by **sharing and definitional reduction** than handwritten LOC. Distinguish by cumulative closure/replay measurements and a named-state/cached-summary perturbation at unchanged theorem strength. Researcher-1 R1.2/R1.8 and researcher-3 R3.6 give concrete upstream mechanisms; their timings are not FVA forecasts.
3. A compact exact-memory summary plus a prefix projection is sufficient for both R1 and R2/R3 without a second full Wasm interpreter. Distinguish by closing the S5→Model adapter and then one general-path join on unchanged bytes.

## P1 — byte-linked workload census and branch/exit probe

Commands (all read-only except outputs in the allowlist):

```bash
/home/eturkes/Projects/fva/.tools/bin/wasm-tools print \
  /home/eturkes/Projects/fva/FVATest/Subjects/Lz4C/lz4-c.wasm \
  > /home/eturkes/Projects/fva/.scratch/u19c2/scientist-1/reprint.wat
# rc 0
cmp /home/eturkes/Projects/fva/.scratch/u19c2/lz4-c.wat \
  /home/eturkes/Projects/fva/.scratch/u19c2/scientist-1/reprint.wat
# rc 0; wasm-tools 1.262.0
uv run --no-project python -I \
  /home/eturkes/Projects/fva/.scratch/u19c2/scientist-1/workload_probe.py \
  /home/eturkes/Projects/fva \
  > /home/eturkes/Projects/fva/.scratch/u19c2/scientist-1/workload_probe.out
# rc 0
```

Positive controls expected funcs 2/3/4 = 550/93/191 static nodes. Observed:

```text
func2: static_nodes=550 loops=7 branches=53 calls=11
func3: static_nodes=93 loops=2 branches=5 calls=0
func4: static_nodes=191 loops=4 branches=12 calls=0
S3: covered_static_nodes=17 loops_entered=1 branch_sites=1 call_sites=1 direct_loads=0 direct_stores=0
S4: covered_static_nodes=18 loops_entered=1 branch_sites=2 call_sites=1 direct_loads=0 direct_stores=0
S5: covered_static_nodes=94 loops_entered=1 branch_sites=7 call_sites=4 direct_loads=2 direct_stores=0
S3-S5 union: func2_static_nodes=129/550 call_sites=6/11
S5 branch directions fixed by hypotheses: 3472=not-taken 3477=taken 3486=taken 3518=not-taken 3522=not-taken 3526=not-taken 3556=taken
S3 body final=br_if 0; S4 body final=br 1 after br_if 0; S4 exit returns to main-loop label continuation
```

Method: line-based census on wasm-tools' one-instruction-per-line WAT; excludes `end`/metadata, includes structured block/loop nodes. S5 removes the two fallback tails at lines 3478–3480 and 3487–3489; source inspection supplies the fixed branch outcomes. This is **not** a Lean proof, dynamic step count, access trace or whole-CFG path enumeration. Copy/Short hashes match; WAT equality links the census to the shipped bytes. The inspected S4 exit agrees with `ctx4`/mainLoop; no exit counterexample found.

## P2 — corpus scope, duplicates and bounded replay

The same `workload_probe.py` reads every row in all five TSVs; no sampling in these counts:

| file | rows | distinct recorded input/capacity pairs | accepted | rejected | maximum input bytes | maximum capacity |
|---|---:|---:|---:|---:|---:|---:|
| cases1.tsv | 3,953 | 3,115 | 1,816 | 2,137 | 595 | 635 |
| cases2.tsv | 79,026 | 78,846 | 49,981 | 29,045 | 830 | 1,507 |
| cases2s.tsv | 13,153 | 13,153 | 8,117 | 5,036 | 830 | 1,507 |
| cases3.tsv | 21,100 | 21,055 | 13,273 | 7,827 | 368 | 479 |
| cases4.tsv | 576 | 240 | 204 | 372 | 22 | 400 |
| union | 117,808 | 103,070 | — | — | 830 | 1,507 |

Output: `corpus_total_rows=117808 unique_input_capacity=103070 repeated_rows=14738`; rc 0. No malformed rows or conflicting expected outcomes observed. This is a fixture-content audit, not a rerun of all Wasm executions or a statistical independence assessment.

Bounded rerun:

```bash
/home/eturkes/Projects/fva/.scratch/u19c2/diff/check-native \
  /home/eturkes/Projects/fva/.scratch/u19c2/diff/cases4.tsv \
  > /home/eturkes/Projects/fva/.scratch/u19c2/scientist-1/model_spotcheck.out
# rc 0; stdout: cases=576 mismatches=0
cmp /home/eturkes/Projects/fva/FVATest/Subjects/Lz4C/Model.lean \
  /home/eturkes/Projects/fva/.scratch/u19c2/diff/Model.lean.bak
# rc 0
```

The supplied native executable was not rebuilt or proven to correspond to the current source; its hash is pinned above. Thus this verifies its behavior on these fixtures, not the source build chain. The current model equals the supplied backup. The reported full zero-mismatch count and 12/12 mutation kills were not independently rerun. Source anchors: `gen.py:12,21`; `gen2.py:14–21`; `gen4.py:10–25` (unused prefix); `Check.lean:19–28` (outcome comparator).

## P3 — synthetic decision-rule sensitivity

Command:

```bash
uv run --no-project python -I \
  /home/eturkes/Projects/fva/.scratch/u19c2/scientist-1/selection_probe.py \
  > /home/eturkes/Projects/fva/.scratch/u19c2/scientist-1/selection_probe.out
# rc 0
```

Output:

```text
infrastructure_excluded: primary_prefers_A=True total_lines_A=10040 total_lines_B=120 replay_ratio_A_B=1
replay_regression_eligible: primary_prefers_A=True total_lines_A=60 total_lines_B=120 replay_ratio_A_B=100
same_work_before_reclassification: primary_prefers_A=False
same_work_60_lines_reclassified_generic: primary_prefers_A=True unchanged_total_A=120 unchanged_total_B=120
twofold_rule: slower=[20.0] faster=[10.0] passes=True
twofold_rule: slower=[20.0, 9.0, 10.0] faster=[10.0, 10.0, 10.0] passes=False
positive_control: identical_costs_do_not_dominate=True
```

These tuples are invented countermodels to claims about the **rule**, not estimates of D+/V/C performance. They show classification sensitivity, ignored first-use cost, permitted replay regression and single-observation instability. No significance claim or probability attaches to them.

## Changes before arms start, ranked by information value

1. **Freeze the semantic decision boundary.** Keep S1–S5, but explicitly acknowledge the single-path S5 limit; freeze I7 soundness/completeness/progress and the exact-memory→prefix adapter. Add a small real multi-exit/join check now if engine selection must claim that capability; otherwise make it the explicit provisional-choice acceptance trigger. This prevents spending three engine budgets on the wrong bottleneck.
2. **Make acceptance and scoring executable.** Pin all S1–S5 statements/common inputs and exact roots; preflight S3–S5 cutpoints/footprints and a planted wrong result. Specify cost aggregates, all three-arm/checker conflicts and what “winner” means. Count all new stage work; retain infrastructure cost rather than hiding it in role bins. Single eligible = bounded readiness only.
3. **Measure growth and replay at the right boundary.** Baseline + cumulative distinct-root closures; all-new-module builds; repeated matched M3 if it may rank, otherwise descriptive only. Pin commands/binaries/host/affinity/limits; preserve raw rc/time/RSS and source snapshots.
4. **Equalize the operational budget and distinguish mechanisms.** Fixed context/continuation policy; same starting assets/prompts/model effort; separate CPU/build resources and recorded waits; D+/V/C primary mechanism and fallback ledger. Preserve incomplete work and censoring causes.
5. **Repair the differential evidence package.** Inert-prefix fix; both buffer orders/boundaries and varied initial output; source/runner hashes, seeds and row-family counts; mutation command/rc/kill-case ledger and a held-out orthogonal corpus. This improves model validation without mistaking fuzz volume for proof.

**Implications:** proceed with a bounded, provisional implementation choice after these protocol repairs; do not restart the broad method survey or add a fourth arm merely to create symmetry. Shared proof judgments and reusable callee/memory-prefix contracts preserve optionality. The next highest-information result is a real decoder join preserving a compact semantic/safety invariant, followed by the whole-domain R1 milestone. Extra copy-only authoring races or repeated timings cannot substitute for that theorem coverage.

## Deliverable validation

- Seed: 10 pattern-bearing lines (preamble + nine seeded rows), rc 0; positive-control file: 1, rc 0.
- Final requested count: 1 (preamble alone), rc 0. Structural/enum check: `claim_rows=14 expected=14 malformed=0 final_marker=scientist-1-DONE-1`, rc 0.
- Final input-hash check: U20, Copy, Short and Model still match the appraisal pins. No arm/proof or shared-build state was changed by this reviewer.

scientist-1-DONE-1
