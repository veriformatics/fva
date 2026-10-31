# scientist-1 — U19 route-comparison check appraisal

| id | claim / design element | verdict (sound / revise / unsound) | reasoning + rival explanations | proposed fix or next test |
|---|---|---|---|---|
| S1 | M1–M5 measure what the decision needs (feasibility at ≈ 877 instructions; re-proof cost per compiler/release change, the fvapi version-proof question) | revise | `overstated`: metrics describe two implementations of one proof, not general proof scaling or release economics. Initial authoring effort, shared setup, failed attempts, export size, independent-checker acceptance, and amortization are missing. | Add M0 effort + complete cost accounting; freeze a theorem/axiom/link acceptance gate; separate one-time, per-artifact and per-repair costs. M5 remains descriptive; feasibility beyond L1 remains open. See S1. |
| S2 | Confounds: one author (MAIN) builds both routes in sequence (learning carries over), route order, effort counted unevenly | revise | `open`: later-route learning and existing direct-stepping infrastructure favor different arms; route labels do not isolate these causes. Shared seam work or changing simp/checker/model settings underfoot can reverse rankings. | Freeze common infrastructure before route work; log initial + repair order, equal effort budgets, failed attempts and borrowed discoveries. Reverse the construction order for repair; use one pinned toolchain/model/harness/checker set. Call this a paired engineering case study, not a causal route comparison. See S2. |
| S3 | M4 perturbation (`-O1` rebuild of the same sources) as a proxy for "next release / next compiler": representativeness, what it cannot show | revise | `overstated`: one optimization-flag change measures local code-generation sensitivity, not next-release or next-compiler maintenance. Unchanged loop = no structural test; rewritten/split loop = legitimate repair difficulty, not permission to pick an easier loop. | Record whole-artifact + selected-region structural deltas before repair; freeze extraction and matching rules; label M4 an optimization perturbation. Release-cost claim remains open until a pinned source-release/compiler-version transition is tested. See S3. |
| S4 | M2/M3 measurement protocol (3 runs, median, same idle host) adequate for the 2× rule | revise | `overstated`: three measurements can expose a large local runtime difference, but no variance, cache policy, module boundary or M3 timing procedure is specified. Runtime repeats do not replicate proof-development effort. | Paired interleaved fresh-process runs after fixed warm-up; fixed dependencies, CPU set, limits and checker versions; report all observations + median + max RSS. Use the 2× label only if observed ranges separate by 2×; otherwise inconclusive. Time export + replay separately; record each checker's status. See S4. |
| S5 | Extrapolation from one 17-instruction loop (M5) to func 2 + callees (paths, nesting, calls): sound basis for the session-bound rule? | unsound | `unsupported`: one selected loop cannot identify a scaling law. Local WAT probe: func 2 has 7 loops / 53 branch opcodes / 11 calls; callees add 6 loops / 17 branches. The “877 instructions” denominator mixes WAT end delimiters with semantic nodes. | Keep M5 descriptive only; replace the linear session predictor with an obligation inventory + one unseen structural-transfer probe (length extension or a callee/branch composition). Start checkpoint 2 only when each remaining obligation has an established proof pattern and explicit effort budget. See S5 + P1. |
| S6 | Ruling rule (lower M4 decides unless ≥ 2× on M1/M2; tie → D): decision-theoretic soundness, thresholds | unsound | `unsupported`: M4 is a vector (edit size, repair effort), “≥ 2× on” does not state which cost is lower, conflicting M1/M2 tradeoffs have no ordering, and the policy ignores feasibility/replay limits. The 2× threshold has no supplied utility basis. | Use acceptance/resource gates first; choose a Pareto-dominant complete route, else keep a tradeoff explicit and use a declared local engineering preference. D as a tie/inconclusive default is permissible policy, not evidence of superior scaling. Report break-even assumptions instead of inventing a future-release distribution. See S6. |
| S7 | What would make checkpoint 1 uninformative, and the cheapest design change that prevents it | revise | `open`: a mis-scoped L1, identical perturbed loop, two effectively identical proof decompositions, unequal trust coverage, or post-hoc stopping would measure something other than the intended choice. A generic byte copy does not exercise decoder parsing/length invariants. | First freeze a well-posed until-exit theorem with exact branch target, footprint scope and memory-address mapping. Audit region change + route dependency graphs before treating M4 as informative; add one predeclared structural-transfer probe only if full-decoder routing is to be decided. Bound effort in advance; record timeout as censored failure, not infeasibility. See S7. |

Scope: pre-run design appraisal, not proof verification or a measured route ranking. Same frozen theorem + real-byte extraction + proof-side-only model = sound foundations. Full-decoder feasibility and future-release cost remain open. `unsound` above applies to the proposed inference/ruling rule, not to either proof method.

Input pins: contract sha256 `97aa69f4e8bbad12151b7825696e0b8ca53b0adb9ad30e0a150b5a79a7a9e434`; WAT `009da55f09edb6afa1dbec3598175739fd9b33c6c8ae584f3b28bebe63678a72`; binary `8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6`. Paths = `/home/eturkes/Projects/fva/` + paths below unless absolute. Research tables were partially filled when inspected; cited rows below only. Their quoted external sources were not independently fetched in this appraisal.

## S1 — estimand + cost accounting

Assumptions required: equal theorem/domain, equal acceptance strength, comparable cost boundaries, representative program structure, representative version transition. First two can be enforced; last two do not follow from this design. A successful L1 proves local feasibility for this loop. It is not an estimate of how often decoders succeed or how cheaply fvapi can update artifact proofs.

M1 = source-size proxy, not development effort or human-review surface. `FVA/Trust/Collect.lean:345–358` defines it as “lines holding a non-blank character outside comments and docstrings”; layout/tactic compression can change it without changing proof difficulty. Both routes may keep identical reviewed specs despite radically different proof code sizes. Count shared footprint/spec additions separately from per-route proof modules; report generated code separately, never hide generated-term costs in M2/M3. R's model definitions and simulation count as proof-side work even though they add no reviewed spec if properly isolated.

Missing primary measurement: M0 initial authoring effort, including failed scripts, theorem restatements, debugging, infrastructure adaptation and validation. Split common setup `S`, route initial effort `I_r`, version binding/rebuild cost, repair effort `U_r`, and export/replay cost. Record elapsed wall time AND active work intervals (exclude external waits, retain build waits separately); agent tokens/model/effort where available. Tokens are not dollars. Record exported declaration closure bytes, generated proof artifacts, `.olean` size, and each checker outcome/resource use.

Rival: R is larger because it pays a reusable abstraction cost once, not because refinement scales worse. Discriminator: reuse the unchanged model/theorems on a second code region/version and report both cumulative and marginal cost. Rival: D is cheaper because mature direct helpers already exist. Discriminator: identify inherited vs newly written helpers; retain the real starting library as the practical comparison, without claiming a method-intrinsic effect.

Knowledge: researcher-1 A2, [Myreen–Gordon–Slind FMCAD 2012, §III](https://www.cl.cam.ac.uk/~mom22/decompilation/fmcad12.pdf): “Decompilation also automatically proves a theorem, which we call a certificate theorem, relating the new function to the machine code from which it was extracted.” Same source: “Any verification that uses such extracted function must prove that the returned cond is equal to true (for relevant input values)”. This supports separating simulation, model correctness and side conditions; it supplies no FVA cost forecast.

## S2 — one author, two histories

Actual unit of analysis = one author/environment × one loop × one perturbation. Three re-elaborations are repeated measurements of that artifact, not three independent route attempts. No route-effect confidence interval or success-rate estimate is justified.

Confounds + observations that distinguish them:
- Learning/order: the second route inherits memory lemmas, entry/exit framing and arithmetic facts. Log when each fact was discovered and where reused; reverse baseline order for repair. This reduces one directional bias, not all carryover.
- Shared work drift: changing `wasm_step`, footprint lemmas, normalization settings or imported modules after D is measured makes R's baseline different. Freeze a common checkpoint. A shared fix triggers both routes' rebuild/replay and a new comparable measurement pair; preserve the failed attempt's cost.
- Treatment fidelity: D already proves a recursive `copyBytes` postcondition; R may merely package the same induction as `copyModel`. Sketch each proof dependency graph. If both have the same segment lemma and same invariant under renaming, conclude “two organizations of one decomposition”, not “refinement beats direct stepping”. Allow natural helper reuse; handicapping D to make R distinct would answer the wrong question.
- Model/harness/grader drift: one author model + effort, Lean/Mathlib hashes, machine, tactic settings, exporter and checker binaries per metric across both arms. Kernel acceptance is deterministic at fixed input; equal axiom/import/statement checks still matter. A model/tool switch is a new condition, not an invisible continuation.
- Stopping: equal predeclared initial/repair effort budgets; every attempt counted; no extending only the favored route. An unfinished route is censored at the budget, not a proof of impossibility.

Existing direct infrastructure is substantial: `FVA/Proof/Lib/Walk.lean:33` composes walks; `FVATest/Subjects/EdgerCpm/BodyContext.lean:40` transports continuation correctness; `BodyRows.lean:58–108` already composes row/callee/column invariants. The practical question is which extension of THIS library wins. A clean-room method comparison would be a different, larger experiment.

## S3 — perturbation validity

`bench/subjects/build-lz4:27–38` fixes `-O2`, clang, freestanding flags, memory layout and shim. Replacing only `-O2` with `-O1` is a sensible controlled code-generation stressor. Label it exactly that. It neither changes source semantics nor samples source-release or compiler-version changes. A future release can change requirements, data layout, calls, code topology, or the model itself.

Before repair, report original/rebuilt whole-artifact hashes; matched-region instruction tree, local renaming, control-flow and call differences; entry/exit correspondence. Matching follows the source operation/effect, not the old function number or the easiest new loop. Preserve split/unrolled/removed regions as findings. If the selected region is unchanged, zero local repair is informative about this perturbation's stability but NOT evidence for robustness to structural change. Still charge real relift/decode/export/recheck costs; a new binary can invalidate those even when the loop is identical.

M4 line accounting: `git diff --numstat` supplies additions and deletions, not a distinct “changed-lines” count. Report `(added, deleted)` on immutable baseline/final snapshots after identical formatting, including newly created helper files. Label `added + deleted` edit churn (a replaced line counts twice); separate mechanical renaming, generated lift churn, and hand-written proof/model changes. Re-proof effort includes locating the new slice, adjusting bindings, failed attempts and full acceptance, not only the last successful Lean command.

Knowledge: researcher-1 A3, [Sewell–Myreen–Klein PLDI 2013, Table 1](https://www.cl.cam.ac.uk/~mom22/pldi13.pdf), quoted headings “gcc -O1” / “gcc -O2”, “Successes 234 145”, “Aborted 26 62”. This demonstrates optimizer configuration can materially alter a verification pipeline, but it is not an effect-size prediction for FVA or a paired direct-vs-model experiment. Same source says “A full decompilation run with proof certificates takes an additional 6–8 hours on modern hardware.” Do not omit binding/certificate stages from end-to-end costs.

## S4 — measurement protocol + 2× interpretation

Three runs are adequate for a cheap descriptive screen only when the difference dwarfs observed variation. Median alone hides unstable runs and an OOM. Specify:
1. Fixed host/CPU set, memory/time limits, Lean/Mathlib/tool hashes and options. Respect the user's other work; defer runs rather than monopolize the desktop. “Idle” is an observed condition, not a sufficient cache/CPU policy.
2. Prebuild identical dependencies once. Each timed invocation starts a fresh Lean process and actually elaborates the specified route module(s); never time a no-op Lake cache hit. Warm each route once, excluded explicitly. Name the complete route-specific file/import boundary; the timed R module must not get its model/simulation free from an uncounted prebuild.
3. Three interleaved paired runs, initial order fixed by a recorded seed. One route invocation per interval; record wall, user/system CPU, exit status and max RSS. Sum sequential module times and take the maximum module RSS for that route's rebuild; label this process-peak metric, not concurrent total memory.
4. Separate export generation, `leanchecker`, and non-Lean-lineage replay. Report raw observations, median and maximum RSS; OOM/timeout stays a failure/censored observation, not a discarded outlier. Store export hashes and declaration lists to show the same obligation closure was checked.
5. “Observed ≥2× runtime separation” only when `min(slower observations) ≥ 2 * max(faster observations)`. Otherwise the threshold decision is inconclusive; a predeclared extra paired block may resolve noise if it affects the choice. This is a conservative descriptive rule, NOT a population confidence bound. M1 is deterministic at fixed formatting and needs no repeated-run test.

M3's original single `leanchecker` check is not FVA's final acceptance target. `FVA/Trust/Replay.lean:34–50` pins default kernels to `leanchecker` + `con-leche`; `Verdict.lean:114–115` requires acceptance outside Lean's lineage. At minimum both routes must clear that same acceptance gate before comparison; exercise the intended paranoid checker set before calling either route a feasible route to checkpoint 2. Checker declines/timeouts are distinct from rejected theorems.

Knowledge: researcher-2 B2, [Lean issue #14331](https://github.com/leanprover/lean4/issues/14331): “~17 s elaboration”, “~30 min”, and “adding `-implicitDefEqProofs` to the final `simp` calls drops the kernel check from ~80min to ~60s.” These are upstream reported measurements, not rerun here, but support measuring kernel replay independently of elaboration. Do not infer a current Lean 4.35 defect: researcher-2 B2 also quotes [4.34 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.34.0/) that #14520 fixes the LNSym `sym_n` exponential blowup.

## S5 — extrapolation is not identified

P1 finds 834 textual semantic instruction nodes across funcs 2–4, versus 877 non-declaration WAT lines INCLUDING 43 `end` delimiters. The distinction alone is modest; the inferential failure is structural. The decoder region contains 13 loops, 70 branch opcodes, 11 call sites and different memory/copy regimes. Counts do not count independent proof obligations, nor does callee code size price its 11 compositions.

The selected region has 17 nodes including its loop header, 16 body instruction lines, 15 through the repeating `br_if`, and a final exit-only `br 2`. Value instructions and administrative context reductions mean even these are not `Ref.step` counts. Define static AST node counts and proven semantic step counts separately. “Seconds per stepped instruction” is descriptive at one fixed segment size; it estimates neither a slope nor fixed setup cost, let alone interaction costs from nested invariants.

Additional representativeness concern (inference, not a proven decoder theorem): on the ordinary no-wrap domain, the surrounding guards give `op ≥ oend−7` and `cpy ≤ oend−5`, so this reachable byte tail executes at most two iterations. Anchors: WAT `3424–3431`, `3847–3887`; upstream C `2422–2429`. The generalized arbitrary-length L1 is valuable as a reusable lemma, but is not even the decoder's long match-copy loop. P2 confirms the guard arithmetic on a bounded integer sanity check; the mathematical bound follows directly by subtraction. No reachability or Wasm equivalence proof was run.

Rivals to a linear forecast: fixed binding overhead dominates the tiny loop; long simplifier terms produce superlinear kernel cost; callee summaries amortize repetitions; data-dependent length/offset invariants dominate everything. All fit one loop's M1–M5 equally well. `Walk.lean:357–360` itself documents why changing the shape of an otherwise similar stepping proof avoids symbolic-`Nat` evaluation “as deep as `4294967295`”.

Cheapest useful replacement: an obligation inventory covering entry, each distinct loop family, branch exits, callee summaries/composition, alias/frame facts, source-format relation, termination, and malformed-input exits. Tag each established / new semantic lemma / untested composition. One predeclared held-out length-extension loop INCLUDING its guard/error exit is the most informative small transfer test after byte copy. Alternatively a full memcpy summary plus one caller composition tests the call seam. Success provides another structural case, not a calibrated full-decoder completion estimate. Any untested class stays explicit; no scalar M5 authorizes finishing the full theorem in one session.

Knowledge: researcher-1 A2 quotes the decompiler's requirement to “separate inner loops from enclosing outer loops where possible”; A3 reports nested-loop aborts. Researcher-3 C4 quotes [Certora's zlib case](https://www.certora.com/blog/formally-verifying-zlib-memory-safety-with-lean): “266 lines of C, 7 loops, and 7 return sites”, “one main-loop invariant with 32 clauses”, “not (yet) functional correctness”, “not about compiled machine code”. These are non-comparable source-level figures, cited solely to show why loop/invariant structure and theorem scope must accompany size.

## S6 — selection policy

Original rule cannot be applied reproducibly:
- Lower M4 can mean fewer changed lines but more repair time, or vice versa.
- “other route is ≥2× on M1 or M2” has no direction for costs; it can literally reward the worse route.
- No resolution for lower M1 but higher M2, failed independent replay, or deadline/memory violation.
- Initial effort, future update count and probability of a requirement/model change have no utility weights. Calling 2× a scientific threshold would invent them.

Recommended local policy: identical accepted theorem first; resource limits next; Pareto dominance of complete implementations next. Consider M0 initial effort, M4 active repair effort, M2 rebuild time and M3 replay time; use M1/churn and dependency localization as secondary diagnostics. A dominance claim based on timings needs the measurement separation in S4. If neither dominates, mark the comparison inconclusive and use D provisionally for this spike (existing machinery / fewer concepts = policy already proposed), unless a documented resource blocker makes only R viable. Report tradeoffs; never rename incomparability “equal” or “tie”. One successful/one budget-exhausted route supports “available within this budget”, not general superiority.

For fvapi, report conditional amortization instead of a release forecast: `cost_r(N) = shared_setup + initial_r + Σ(version_binding + repair_r + rebuild_r + export_r + replay_r)`. If R pays more initially and repairs are cheaper in this one perturbation, show a break-even N under the explicit assumption that those costs repeat. Do not assign a forecast probability or expected N from one transition. A model that must change with a new requirement loses part of the assumed reuse.

## S7 — informativeness + theorem hygiene

Before either route: replace the prose L1 with one frozen elaborated statement and exact extraction equation. Check unsigned address interpretation, `inst.mems[0] = ma`, store-address framing, real locals 18/2/3, no-wrap bounds, arbitrary irrelevant locals, control-stack shape, and final branch target. The source byte-copy loop's compiled exit is `br 2`, WAT `3904`, not lexical fall-through.

Critical scope ambiguity: contract A2 defines `Throughout H P c` over EVERY reachable state. L1 says “on the way” but uses A2 under arbitrary continuation. An allowed continuation can store outside `[op, cpy)` immediately after the loop; ordinary `Throughout` then fails although the loop is correct. Likewise A3's finite safe walk needs safety at its endpoint to carry global `Throughout` backward. Use a before-first-exit safety predicate + total reachability of that exit, or a continuation-style theorem assuming correctness/safety of the exit continuation. `BodyContext.lean:40–45` already uses an explicit `hk : Must ... successor` premise. This is a statement-validity issue, not evidence that either route is hard.

Route R must prove coverage of ALL intermediate Wasm accesses and termination, not just endpoint memory equality or one sampled trace. Its model recursion and simulation can share the logical copy specification, but prove the actual bytes implement it. Permit finite segment/stuttering simulations if a compiler transformation changes cutpoints; requiring a literal one-machine-iteration ↔ one-model-step bijection would turn compiler scheduling into an artificial failure. Such a change must preserve the same external L1, with its engineering cost counted.

Minimum failure taxonomy: false/ill-posed statement; missing reusable semantic lemma; unresolved subject invariant; elaboration limit; exporter/checker limit; exhausted effort budget. Keep last failed obligation + command/rc and progress achieved. A negative attempt distinguishes these causes only if logged. Claiming “no path to verification” from this spike is unsupported.

## Pasteable protocol replacement

> Checkpoint 1 estimates local proof-construction and repair costs for one frozen loop theorem; it does not estimate full-decoder completion time or future-release cost. Freeze L1's elaborated statement, actual-byte extraction, entry/exit control contexts, until-exit footprint scope, acceptance gate and resource/effort budgets before either route. Common footprint/context infrastructure is one separately recorded setup cost. Both routes prove the same theorem with the same permitted axioms and checker set.
>
> M0 = initial active effort, elapsed time, failed attempts and validation waits, split common/route-specific. M1 = formatted `codeLines`, split shared, route-specific semantic stepping/simulation, model definitions/reasoning and generated code; record reviewed-surface delta separately. M2 = complete route-specific elaboration/rebuild wall time and max RSS, with identical prebuilt dependencies, fixed CPU set/limits and fresh processes; warm once and measure three interleaved paired runs, preserving all observations/statuses. M3 = export bytes/time/RSS plus per-checker replay time/RSS/status on the same declared closure; default independent replay is required for comparison, intended paranoid acceptance before route promotion. Preserve raw observations, tool/input hashes and commands.
>
> M4 = one fixed `-O2`→`-O1` code-generation perturbation, same sources/compiler/other flags. Record whole-artifact and selected-region deltas before repair. Re-establish the SAME external theorem on the corresponding region, including locating/extracting it, binding to bytes, failed repairs and full acceptance. Report added and deleted hand-written lines separately, mechanical/generated churn separately, active repair effort and full elapsed cost. Reverse baseline route order for repair; log discovery reuse. An unchanged region does not test structural-change robustness. A split/removed region remains an outcome, never grounds for silently substituting an easier loop. M5 = descriptive lines/time per explicitly defined static node or proved semantic step; no linear full-program extrapolation.
>
> Selection: complete equal-strength proofs within the fixed limits are eligible. Prefer a Pareto-dominant route on initial effort, active repair effort, rebuild and replay cost; M1/churn explain the tradeoff. A runtime ≥2× label requires `min(slower) ≥ 2×max(faster)` across the paired measurements; otherwise that comparison is inconclusive. If eligible routes trade off, record inconclusive and choose D provisionally for this spike, not as a general scaling result. Budget exhaustion means not completed under these conditions.
>
> Session routing: create an obligation inventory for func 2 + its callees, naming each new loop/invariant/call/error-exit class and its established proof pattern. If full-decoder work is proposed in this session, first run one fixed held-out structural-transfer probe; its target and budget are recorded before either route is measured. Attempt checkpoint 2 only when all remaining classes have demonstrated reusable patterns and the inventory's explicit conservative effort allowance fits the remaining session budget. Otherwise close checkpoint 1 as a bounded result and route the full theorem to the longer phase. No version-proof economy claim follows until a source-release/compiler-version transition is separately tested.

## P1 — targeted WAT structure probe

Question settled: does the stated instruction count mean the same unit in the small loop and full-decoder extrapolation? No. Positive controls = three function summaries; selected slice has one load, one store, one backedge and one exit branch.

Command (read-only, no Lean build):
```bash
awk '
/^[[:space:]]*\(func \(;[234];\)/ {f=$2; start=NR; raw=0; semantic=0; ends=0; loops=0; branches=0; calls=0; loads=0; stores=0; next}
f && /^[[:space:]]*\)$/ {printf "func%s header=%d end=%d body_lines=%d semantic_nodes=%d end_delimiters=%d loops=%d branches=%d calls=%d loads=%d stores=%d\n", f,start,NR,raw,semantic,ends,loops,branches,calls,loads,stores; f=""; next}
f {raw++; if ($1 ~ /^\(/) next; if ($1 == "end" || $1 == "else") {ends++; next}; semantic++; if ($1 == "loop") loops++; if ($1 ~ /^(br|br_if|br_table|if)$/) branches++; if ($1 == "call") calls++; if ($1 ~ /\.load/) loads++; if ($1 ~ /\.store/) stores++}
' /home/eturkes/Projects/fva/.scratch/u19/wat/lz4-c.wat
rc=$?; printf 'structure_rc=%d\n' "$rc"
```
Output:
```text
func(;2;) header=3381 end=3964 body_lines=582 semantic_nodes=550 end_delimiters=31 loops=7 branches=53 calls=11 loads=15 stores=6
func(;3;) header=3965 end=4064 body_lines=98 semantic_nodes=93 end_delimiters=4 loops=2 branches=5 calls=0 loads=5 stores=5
func(;4;) header=4065 end=4266 body_lines=200 semantic_nodes=191 end_delimiters=8 loops=4 branches=12 calls=0 loads=10 stores=10
structure_rc=0
```
`body_lines` includes one local-declaration line per function. `semantic_nodes` is a textual count excluding declarations/closing delimiters, not a verified AST traversal. Branches include unconditional/conditional branches, not independent execution paths. Counts cover these three complete functions only.

Command:
```bash
awk 'BEGIN {n=0; ordinary=0; loads=0; stores=0; back=0; exits=0} NR>=3888 && NR<=3904 {n++; if (NR>3888) ordinary++; if ($1 ~ /\.load/) loads++; if ($1 ~ /\.store/) stores++; if ($1=="br_if") back++; if ($1=="br") exits++} END {printf "positive_control_loads=%d expected=1; stores=%d expected=1; backedges=%d expected=1; exits=%d expected=1\n",loads,stores,back,exits; printf "selected_nodes_including_loop=%d body_nodes=%d backedge_instruction_lines=%d exit_instruction_lines=%d\n", n,ordinary,ordinary-1,ordinary}' /home/eturkes/Projects/fva/.scratch/u19/wat/lz4-c.wat
rc=$?; printf 'loop_count_rc=%d\n' "$rc"
```
Output:
```text
positive_control_loads=1 expected=1; stores=1 expected=1; backedges=1 expected=1; exits=1 expected=1
selected_nodes_including_loop=17 body_nodes=16 backedge_instruction_lines=15 exit_instruction_lines=16
loop_count_rc=0
```
Initial loop-count attempt used reserved awk identifier `exit`: parser `syntax error`, rc 1. Corrected to `exits`; only the successful output above informs the count.

WAT provenance check:
```bash
set -o pipefail
/home/eturkes/Projects/fva/.tools/bin/wasm-tools print /home/eturkes/Projects/fva/bench/subjects/wasm/lz4-c.wasm | sha256sum
rc=$?; printf 'wat_reprint_digest_rc=%d\n' "$rc"
sha256sum /home/eturkes/Projects/fva/.scratch/u19/wat/lz4-c.wat
rc=$?; printf 'supplied_wat_digest_rc=%d\n' "$rc"
```
Output: both digests `009da55f09edb6afa1dbec3598175739fd9b33c6c8ae584f3b28bebe63678a72`; both rc 0.

## P2 — guarded byte-tail arithmetic sanity check

Question: is the sampled loop the decoder's potentially long byte-copy path? Under surrounding no-wrap guards, no: `after = max(op, oend−7)`; `cpy ≤ oend−5`; remaining count ≤2. This is an inference from inspected source/WAT, not a machine-checked whole-decoder invariant.

Command translates `oend` to 0 and samples nearby integer offsets:
```bash
awk 'BEGIN {m=0; hits=0; for (op=-10;op<=10;op++) for(cpy=-10;cpy<=-5;cpy++) {after=(op < -7 ? -7 : op); count=(cpy>after ? cpy-after : 0); if(count>m)m=count; if(count==2)hits++} printf "guard_arithmetic_max_tail=%d positive_two_cases=%d\n",m,hits}'
rc=$?; printf 'bounded_arithmetic_rc=%d\n' "$rc"
```
Output:
```text
guard_arithmetic_max_tail=2 positive_two_cases=4
bounded_arithmetic_rc=0
```
Coverage limit: bounded integer sanity check; no bitvector wrap, reachability, memory effects or compilation equivalence tested. The general inequality follows from the stated bounds, whose validity over the full decoder remains a proof obligation.

## Implications + next analyses, ranked by information value

1. Fix/freeze L1 and continuation safety before measurements. Otherwise a failure diagnoses the contract, not the proof route. Lowest-cost prevention of a wholly uninterpretable result.
2. Inspect the `-O1` matched region before repair; preserve structural delta + acceptance failures. This decides what M4 can actually tell us.
3. Run equal-budget two-route L1 construction/repair with complete effort + independent-replay accounting. Deliver a local engineering result, including an inconclusive outcome when appropriate.
4. If session routing still depends on scale, one held-out length-extension + error-exit or callee-composition proof, selected in advance, beats more runtime repetitions of byte copy. It tests a new proof-obligation class; it still cannot certify a universal scaling law.
5. For fvapi economics, test a pinned released-source or compiler-version transition with frozen requirements/model and record which changes invalidate bindings, simulation, model proof or spec. Later test a requirement-changing release separately. Distinguish proof reuse, fresh proof generation and client checking costs.

Bold testable hypothesis: repair cost is driven more by the number of changed proof-summary interfaces/cutpoints than by changed instruction count or the D/R label. This predicts a modular direct proof can be as stable as an explicit model, while a source-shaped refinement can break under optimization. The dependency/invalidation ledger above gives the first separating observation.

Not run: Lean builds, either proof route, `-O1` rebuild, timing benchmarks, kernel replay, full gate, external-source re-fetch. No route performance numbers or full-decoder feasibility were confirmed. Inspected proofs establish existing technique shape only; this appraisal does not re-verify them. No repo files changed; this validator-input report alone was edited.

scientist-1-DONE-1

