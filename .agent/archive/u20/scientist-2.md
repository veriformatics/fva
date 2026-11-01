# scientist-2 — U20 round-2 design appraisal

| id | claim / question | verdict | evidence | repair or next test |
|---|---|---|---|---|
| C1 | Round 1 is “no lone dominant arm” under frozen rule 3, whatever (b)/(c)/(e) show | **supported**, conditional on C and D+ both remaining eligible | `docs/contracts/U20-proof-scaling.md:32–36,59–60`: C total 1650 < 1682, but S5 368 > 341; V's first four stages total 1785. The necessary line-count comparisons already fail. P1 recomputes the crossing; ±1 line per stage preserves it. | Complete checker/resource eligibility. If filtering leaves one arm, apply rule 5: bounded readiness, not superiority. Calling C/D “eligible” before those checks is premature. |
| C2 | SegC discriminates engines rather than mostly measuring loop-induction skill that both can delegate | **overstated** as engine isolation; **open** which burden will dominate | `Seg.lean:103–112,159–175` below: one byte-dependent extension loop, a recursive target function, preserved state and exits. WAT slice: 2 static loads, 7 conditional branches, 0 calls/stores. Shared `Cut/SegA.lean:69,92,109` already supplies functional exit bridges. | Discriminant = added execution-engine glue/rules **versus** generic induction/model arithmetic and cutpoint plumbing, with exact reused declarations. A gap in the latter supports author/library readiness, not an isolated engine advantage. See C2. |
| C3 | Round 2 adds/keeps author × engine, host contention, shared-main-lemma reuse and S1–S5 carryover confounds | **supported**; most bias directions are unconfirmed | Contract `:16,64–65`: one continuing author per engine; three concurrent builds on eight threads; shared amended main. Round-1 tables already show unequal inherited infrastructure. P2: both arms have strong S4/S3 reuse, not independent replications. | Record actual base/tool/model metadata, declaration provenance, observed waits and failure causes. Treat “same host” as shared exposure, not equal penalty. Do not retrospectively forbid available lemmas. |
| C4 | Round-2 (a)/(b) + reuse notes support the qualitative ruling | **supported** for bounded marginal readiness/cost; **unsupported** for causal superiority or decoder-wide scaling | Contract `:63–66` deliberately makes this one needed cutpoint, three hours per arm, advisory only. `Seg.lean:167` caps memory at 2 MiB. One author–engine pairing per arm cannot estimate author variation or separate it from engine effects. | Report the complete cost vector, completion/failure class and dependency audit. No new dominance rule, aggregate winner score, per-instruction extrapolation, or claim of smaller human-review surface. |
| C5 | “I7 fit neutralized by Sim.lean” | **supported** for downstream logical interface compatibility; **overstated** for total I7 proof cost | `Sim.lean:267–299` accepts `hC : SegC`, uses only its specified exits, and maps `extM` to `Model.ext`. `Top.lean:7–14` remains conditional on cutpoints. No engine-specific premise enters this consumer. | Keep the common simulation as a common/sunk cost. Preserve each engine's cost of reaching the exact interface, its internal invariants/adapters and proof-term/checker costs. |
| C6 | Protocol changes worth making before results steer the ruling | **supported**: additive accounting and acceptance checks only | Contract `:18,23–26,32–36,65–66` already requires mechanism boundaries, cost/reuse reports and eventual checks. The central attribution gaps can be exposed without another proof task or a changed target. | Freeze the C2 decomposition/provenance fields now; accept/replay the exact SegC roots after harvest; keep the existing target, budgets and selection rule. No round 3. Costs = report classification + planned checking, not new authoring. See C6. |

Paths in the table: `Seg.lean`, `Sim.lean`, `Top.lean`, `Ext.lean`, `Cut/SegA.lean` = `FVATest/Subjects/Lz4C/…`; “Contract” = `docs/contracts/U20-proof-scaling.md`. Findings = C1–C6, details below.

Scope: design appraisal of the local proof-engine choice, not appraisal of unseen round-2 results. Read the complete contract and Seg definitions; Sim header/consumer; Top header/instance facts; only the requested round-1 result tables. Inspected the committed extension statement and SegA bridge lemmas to check shared-work confounding. No arm contacted, round-2 work inspected, build run, kernel replay run, or repository/worktree edit made. Only this validator input is written.

## C1 — Necessary comparisons settle dominance, not eligibility

Rule 3 is conjunctive. C fails the S5 coordinate by 27 lines; D+ fails total by 32. V's cumulative first four stages already exceed both totals, under the contract's stage-by-stage new/changed-code accounting. No future value of a different conjunct repairs a failed line comparison. The crossing survives a conservative sensitivity allowance of ±1 line **per stage per arm**: minimum remaining total gap 22, S5 gap 25 (P1).

Those are small descriptive artifact differences: C's total advantage = 1.90% of D+'s; D+'s S5 advantage = 7.34% of C's. They are neither statistical significance nor an established practical-importance threshold. MAIN's frozen counter governs; the reports' role splits differ slightly from that counter, as the contract acknowledges at `:59`.

Eligibility is separate. Both default checkers and the ≤10-minute bounds remain required (`:32,35`); the contract expressly says M2/M3 are pending (`:57,69`). A checker rejection or resource disqualification can change the candidate set. “No pairwise dominance on the reported vectors” is settled; “both finalists fully eligible” is not. A singleton then supports readiness on this slice, not an engine-superiority claim (`:36`).

## C2 — Good next obligation; weak isolation of the engine

### What the check adds

The WAT at printed lines 3704–3768 has an immediate exit for `ml0 ≠ 15`, a bound check, the first byte, a loop controlled by both position and byte value, and a final arithmetic guard. The loop body at 3735–3756 contains 22 instructions. A proof must relate arbitrary source bytes to `extM`, establish progress/termination, preserve constant/live locals and memory, and route normal/error exits through the right contexts. Unlike a fixed-count copy loop, the trip count depends on bytes. This is relevant incremental coverage of the actual decoder.

But the novelty is principally **symbolic loop induction plus its state/model relation**, not a large new straight-line or call-composition workload: no stores or calls occur in the slice; most branch/call/context machinery was already exercised by S5. `extM` gives both engines the same recursive mathematical target (`Seg.lean:103–112`), and `AtX4`/`Err` deliberately abstract dead locals (`:114–117,148–154`). These simplify endpoint plumbing; they do not provide the missing loop proof.

The loop class is new to these arms' frozen S1–S5 workload, not new to the project. `Ext.lean:5–16,40–64` already states the literal-extension loop with sentinel, bound and overflow exits. `Cut/SegA.lean:69–127` has `extM_normal`, `extM_bound_exit`, `extM_overflow_exit`: generic functional bridges, not proofs of SegC's different code/context/local allocation. Their reuse can erase much of the novel mathematical work for either arm. Their module importing a direct-stepping theorem does **not** by itself make these pure functional lemmas engine-specific; inspect the declarations actually used and their dependencies.

### Reachable behavior is narrower than the static guards

From the frozen premises:

- `n ≤ 2097152 − 131072 = 1966080`;
- starting at `j ≥ src`, at most `max 0 (n−4) ≤ 1966076` bytes can pass the extension bound;
- each byte ≤255, initial extension accumulator = 0, hence every read prefix sums to at most 501349380;
- adding the field's 15 gives at most 501349395 < 2^31;
- `o' < 2^31` implies unsigned `~o' ≥ 2^31`.

Thus the signed accumulation-overflow branch and the final `length > ~o'` branch cannot fire within SegC's domain. Proving their infeasibility still costs proof effort; it is not coverage of reachable overflow failures. Sentinel termination and input-bound failure remain genuinely data-dependent. P1 checks the arithmetic; this is a source-based bound argument, **not a new kernel-checked theorem**. No counterexample to SegC was found; its full validity is unconfirmed by this read-only appraisal.

### The observable that separates the rival explanations

Keep total added/changed lines and M0 unchanged. Add a per-declaration attribution, with mixed declarations left mixed:

1. **Execution mechanism:** stepping/evaluator rules, symbolic execution of this code, branch/context transport, and any newly verified loop rule that belongs to that engine.
2. **Mathematical loop/model work:** induction over bytes/fuel, accumulated-sum and bounds lemmas, termination reasoning, and `extM` correspondence independent of the execution representation.
3. **Cutpoint plumbing:** locals preservation, exit packaging, footprints and exact interface adapters.
4. **Reuse:** exact declaration + origin (own S1–S5 / common main / new), used unchanged versus adapted; list the execution theorem actually discharging the loop.

Report the slow/failed obligations and approximate effort attribution only when supported by logs; do not fabricate active-time estimates from M0. A short final theorem can hide hundreds of imported/added lines.

- **Engine explanation:** under comparable mathematical facts, one engine needs fewer new block/loop rules or residual execution obligations, with the assigned mechanism genuinely handling the loop. This is local evidence of engine reuse/ergonomics, still author-confounded.
- **Generic-lemma/author explanation:** execution wrappers are similarly small, while the difference is induction discovery, arithmetic, shared lemma uptake or endpoint bookkeeping. This supports readiness of these implementations/authors, not “evaluator beats stepping.”

A new engine-specific general loop rule is a real library investment, not overhead to discard from (a). Conversely, importing an already-proved compiled-loop execution theorem can bypass the intended engine comparison even if its signature is highly generic. Audit use, not names.

## C3 — Confounds and direction

| factor | fit to this design; direction | observation that separates explanations |
|---|---|---|
| Author × engine | Perfectly paired, n=1 each (`Contract:16,36,64`). Continuing the same author preserves learning but does not cancel skill/strategy differences. Direction unconfirmed. | Failure/effort decomposition can identify a mathematical versus engine obstruction; it cannot estimate a causal author-adjusted engine effect. |
| Contended M0 | Three builds/eight threads and waits included (`:23,65`). A more resource-hungry proof may suffer more, and staggered phases see different contention. Equal machine ≠ equal slowdown. | Wall interval, build/queue waits available from logs, resource failures, and later quiet-host build timings. No unsupported subtraction of “background time.” |
| Common main lemmas | Equal availability is a legitimate shared starting point, but use/familiarity may differ. The extM bridges reduce generic work; direct compiled-code lemmas could preferentially aid the stepper or bypass an engine. Actual direction unconfirmed. | Exact base SHA and used-declaration provenance; separate mathematical facts from execution summaries. Keep their original construction as common/sunk cost, not a zero-cost claim about development from scratch. |
| Own S1–S5 carryover | Intended for the operational question “what is next cheapest here,” a confound for an intrinsic engine ranking. C and D+ inherit different libraries and contexts. | New versus reused declarations. P2: S4/S3 statement-line ratios C 0.236, D+ 0.196; elapsed ratios C 0.190, D+ 0.156. Both already reuse strongly. Five stages are not five independent authors. |
| Task chosen after round 1 | Needed decoder cutpoint + freezing before its results restrain cherry-picking. Still, one selected loop class is not a holdout representative of all remaining decoder work. Direction unconfirmed. | Keep round 1 intact, show all round-2 outcomes and unresolved inventory classes; apply the stated “no round 3.” |
| Model/tool/harness state | Same lane/equal effort promised (`:16`); exact resumed model versions, context/compaction state and tool pins were not inspected. Drift is neither established nor ruled out. | Actual launch metadata, common base/toolchain, CPU/memory limits and resolved model/effort. A lane alias alone is not a version audit. |

The contract's prior-method rationale says the architecture layers are composable and “their bulk is invariant reconstruction, not instruction stepping” (`:39`). SegC's shape is consistent with that expectation, not independent empirical confirmation of it. The cited research reports/primary papers were not inspected here; no external-literature claim is independently validated by this appraisal.

## C4 — What the qualitative ruling can carry

**Can carry:** exact statement completion; bounded observed cost of extending each existing engine/library/author pairing to this useful, fixed cutpoint; a documented reusable mechanism or blocking obligation; checked resource feasibility. A failed three-hour attempt means “not completed under this cap, starting state and load,” with its last obligation—not impossibility.

**Cannot carry:** causal engine superiority; population means or statistical power; automatic invariant discovery; decoder-wide R1–R3 completion; performance on larger memories, other loop classes or other binaries; source-level maintenance cost; or human-review-size/readability gains. Both arms prove the same proof-side interface, and the contract explicitly excludes proof-library code from the trusted review surface (`:3`). Proof authoring lines are not spec-review lines.

No inferential test is justified by the design. Repeated build/replay runs measure machine variability, not author variation. Multiple metrics and a task selected after round 1 make a best-looking ratio particularly weak evidence. Preserve the vector and the inconclusive result; do not append SegC to a newly invented total/S5 dominance test. If only (a)/(b) are available, computational scalability remains open until (c)/(e) and eligibility are checked.

## C5 — Interface compatibility is genuinely common

`contX3Sim` takes an arbitrary proof of `SegC` (`Sim.lean:267`) and applies it at `:282–283`; its three-way continuation at `:289–299` depends only on the specified results. `extM_eq` (`:17–37`) and the surrounding adapters handle the memory/model correspondence outside either engine. The prepared instance has the required 2 MiB memory (`Top.lean:28`); the top-level statements remain conditional (`:7–14`).

Therefore engine substitution does not require a different downstream simulation, **once the same SegC statement is established**. This settles one narrow “I7 fit” concern. The costs of establishing that statement, exposing usable facts inside its proof, future maintenance, and proof-term export/replay are not equalized. The shared interface relocates those costs; it does not remove them. This is source inspection of the consumer, not a rerun of its kernel check.

## C6 — Recommended completion, ranked by information value

1. **Freeze additive mechanism/provenance reporting now.** C2's categories + actual base/model/tool metadata + blocking obligations. Highest information value for the central question; cost = declaration classification and report notes. Do not alter ongoing authors' proof strategy, allowed lemmas, target or budget. If precise time attribution was not logged, leave it unconfirmed.
2. **Accept and replay exact roots at harvest.** Type-check each result against frozen `SegC`, inspect axioms and assigned mechanism, retain failed commands/rc, and include SegC in the planned independent-checker harvest. Confirm C/D's round-1 eligibility separately. Cost = acceptance/replay of two additional roots plus the already-planned checks; no new authoring task. This appraisal has not run them.
3. **Use the quiet-host measurements already planned.** Same toolchain, prebuilt imports, interleaved pinned-CPU runs; record fresh-build/import scope and incremental closure size. Cost = the existing M2/M3 plan, with any SegC extension named explicitly. Keep contended M0 as an operational observation, not a repaired speed benchmark.
4. **Close with the limits intact.** Map the observed mechanism gain or obstruction to the remaining inventory; retain “inconclusive” if attribution stays ambiguous. No third competitive task. A provisional local choice can be a policy/maintenance ruling rather than a claimed empirical superiority.

Process note: contract `:3` calls for scientist design appraisal before the runs; `:69` says round 2 is already launched. This review is **post-launch, pre-result inspection/grading**, not pre-run validation. The frozen target still protects against outcome-driven target edits; additive accounting now does not retroactively make the appraisal prospective.

Implication/hypothesis worth testing against the existing reports: a common invariant/semantic library may explain more of SegC's cost than the stepping-versus-evaluation boundary. If the declaration audit bears that out, further engine ranking has low information value; invest in shared obligations and select the locally maintainable engine without claiming general superiority. If execution glue dominates instead, the check has located an engine-specific scaling bottleneck. Either finding is useful without another round.

## Probe record

### P1 — Dominance sensitivity + reachable-overflow arithmetic

Command (plain arithmetic on the frozen contract/statement constants; no build):

```sh
awk 'BEGIN {
 c=511+632+113+26+368; d=505+638+164+34+341; v=553+778+335+119;
 printf "C_total=%d D_total=%d V_S1toS4=%d\n",c,d,v;
 printf "C_le_D_on_both_a=%d D_le_C_on_both_a=%d V_can_dominate_either_on_total=%d\n",(c<=d && 368<=341),(d<=c && 341<=368),(v<=c || v<=d);
 printf "min_total_gap_at_plusminus_1_per_stage=%d min_S5_gap_at_plusminus_1=%d\n",(d-5)-(c+5),(368-1)-(341+1);
 n=2097152-131072; reads=n-4; acc=255*reads;
 printf "max_n=%d max_reads=%d acc_bound=%d acc_plus_15=%d\n",n,reads,acc,acc+15;
 printf "signed_overflow_possible_under_bound=%d final_guard_possible_under_o_lt_2pow31=%d\n",(acc>=2147483648),(acc+15>2147483648);
}'; rc=$?; printf 'rc=%s\n' "$rc"
```

Output (same computations as the two arithmetic probes):

```text
C_total=1650 D_total=1682 V_S1toS4=1785
C_le_D_on_both_a=0 D_le_C_on_both_a=0 V_can_dominate_either_on_total=0
min_total_gap_at_plusminus_1_per_stage=22 min_S5_gap_at_plusminus_1=25
max_n=1966080 max_reads=1966076 acc_bound=501349380 acc_plus_15=501349395
signed_overflow_possible_under_bound=0 final_guard_possible_under_o_lt_2pow31=0
rc=0
```

Bound is conservative: the maximal sum permits every read byte to be 255, even though successful termination needs a final byte other than 255. Prefix sums are nonnegative, so the total upper bound also bounds every intermediate sum. This proves no new Lean theorem and executes no Wasm input.

### P2 — Table-only recomputation of first-use/reuse intervals

```sh
awk -F'|' '
function secs(t,a) { gsub(/^ +| +$/, "",t); split(substr(t,12,8),a,":"); return a[1]*3600+a[2]*60+a[3] }
FNR==1 { inside=0 }
/^## / { inside=($0=="## Per statement") }
inside && /^\| S[1-5] / {
 count++; arm=(FILENAME ~ /spike-c/ ? "C" : "D+"); stmt=$2;
 gsub(/^ +| +$/, "",stmt); split(stmt,s," "); dt=secs($6)-secs($5); lines=$8+0;
 printf "%s %s elapsed_s=%d statement_lines=%d\n",arm,s[1],dt,lines;
 if(s[1]=="S3") { t3[arm]=dt; l3[arm]=lines }
 if(s[1]=="S4") printf "%s S4_over_S3 elapsed_ratio=%.3f statement_line_ratio=%.3f\n",arm,dt/t3[arm],lines/l3[arm]
}
END { printf "stage_rows=%d\n",count; if(count!=10) exit 1 }
' /home/eturkes/Projects/fva/.scratch/u19c2/spike-c/report.md \
  /home/eturkes/Projects/fva/.scratch/u19c2/spike-d/report.md
rc=$?; printf 'table_probe_rc=%s\n' "$rc"
```

```text
C S1 elapsed_s=2026 statement_lines=281
C S2 elapsed_s=2600 statement_lines=616
C S3 elapsed_s=300 statement_lines=110
C S4 elapsed_s=57 statement_lines=26
C S4_over_S3 elapsed_ratio=0.190 statement_line_ratio=0.236
C S5 elapsed_s=2048 statement_lines=349
D+ S1 elapsed_s=2806 statement_lines=222
D+ S2 elapsed_s=2173 statement_lines=568
D+ S3 elapsed_s=537 statement_lines=138
D+ S4 elapsed_s=84 statement_lines=27
D+ S4_over_S3 elapsed_ratio=0.156 statement_line_ratio=0.196
D+ S5 elapsed_s=3569 statement_lines=287
stage_rows=10
table_probe_rc=0
```

First attempt matched all `S1…S5` rows rather than the named section: it reached the report's short checkpoint table and failed, `fatal: division by zero attempted`, rc 2. Discarded that extraction; section-anchored rerun above checked the expected 10 stage rows. These ratios use the reports' statement-specific line column, not rule 3's whole-stage metric.

### P3 — Source identity + WAT shape

Commands actually run:

```sh
sha256sum /home/eturkes/Projects/fva/FVATest/Subjects/Lz4C/Seg.lean
git -C /home/eturkes/Projects/fva diff --quiet HEAD -- \
  FVATest/Subjects/Lz4C/Ext.lean FVATest/Subjects/Lz4C/Cut/SegA.lean
rc=$?; printf 'shared_diff_rc=%s\n' "$rc"
set -o pipefail
/home/eturkes/Projects/fva/.tools/bin/wasm-tools print \
  /home/eturkes/Projects/fva/FVATest/Subjects/Lz4C/lz4-c.wasm |
  awk 'NR>=3704 && NR<=3768 {
    printf "%d:%s\n",NR,$0;
    if($0 ~ /i32.load8_u/) loads++; if($0 ~ /br_if/) brs++;
    if($0 ~ /^[[:space:]]*call /) calls++; if($0 ~ /i32.store/) stores++
  } END { printf "slice_counts: load8=%d conditional_branches=%d direct_calls=%d stores=%d\n",loads,brs,calls,stores }'
rc=$?; printf 'wat_index_rc=%s\n' "$rc"
```

Observed: Seg SHA256 `ff4cbe5871a98c2adaa946554a44918e6ff93c0120ac93004348fa0cf8077001` = frozen contract; both shared sources tracked and identical to HEAD (`shared_diff_rc=0`). WAT output was read in full for the requested 65-line slice. Selected load-bearing output:

```text
3723:                    i32.load8_u
3734:                  loop ;; label = @8
3741:                    br_if 4 (;@4;)
3744:                    i32.load8_u
3749:                    i32.lt_s
3750:                    br_if 4 (;@4;)
3756:                    br_if 0 (;@8;)
3766:                i32.gt_u
3767:                br_if 4 (;@2;)
slice_counts: load8=2 conditional_branches=7 direct_calls=0 stores=0
wat_index_rc=0
```

Positive shape controls = the 2 expected loads and 7 branch sites in the inspected slice; no-call/no-store counts are restricted to that slice. No independent checker, complete-decoder proof, host contention trace or launch-metadata audit was run.

scientist-2-DONE-1
