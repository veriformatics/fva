# scientist-1 — U19 checkpoint-1 result appraisal

| id | claim | verdict (supported / overstated / unsupported / open) | reasoning + rivals | fix or next test |
|---|---|---|---|---|
| E1 | Ruling follows the frozen protocol (Pareto, 2× rule, inconclusive → D provisional); order-effect interpretation is honest | overstated | The **ruling is supported**: eligible historical proofs, conflicting effort rankings, no M2 range separation, no defensible M3 ranking ⇒ inconclusive, D by policy. “Order effect dominates” is stronger than one sequential pair identifies; copying/learning is documented, its causal share is not. | Say “the second implementation was quicker in both phases, with documented borrowing; order and route effects cannot be separated.” Keep D provisional, not the winner or the scaling route. E1, P1–P3. |
| E2 | M1 split supports “stepping dominates / model reuse offset by binding + composition” | overstated | Archived totals recompute. Machine-facing iteration/induction proofs are the majority even under symmetric grouping. The groups also contain arithmetic, state framing and invariant maintenance; source lines do not establish runtime/effort dominance. Reused 68 lines vs 59 newly written lines is not a causal cost-offset estimate. | Report source-size concentration and concrete reuse, not a necessary full-re-step cost or negative refinement result. Symmetric grouping: D 74.7%/76.1%, R 61.0%/63.7% for O2/O1. E2, P1. |
| E3 | M4 interpretation: what -O1 shows and does not show for release/version economics | overstated | It demonstrates two successful repairs for one optimizer-flag transition with real structural change. It does not estimate next-release cost, establish that instruction proofs cannot survive, or show that only the R model is reusable: O1 D reuses its O2 sum helpers too. | Restrict to this transition and the chosen repair strategy. Separate version-addition LOC, authoring intervals, existing helper/model reuse, and complete acceptance/rebuild costs. E3. |
| E4 | I4–I9 undemonstrated ⇒ partial close and checkpoint 2 routed to IMPLEMENT; what IMPLEMENT should measure first | supported | The frozen gate requires every obligation class to have a demonstrated pattern. Several essential classes remain unproved, so checkpoint 2 must not start here. This is unmet readiness evidence, not a failed full-decoder proof or a lower bound on required time. I2/I3/I10 also need narrower “established pattern” wording. | Close partial; user rules the longer phase. First test a minimal I4 call-summary composition while scoping an I7 one-sequence semantic invariant; measure first-use vs reuse effort, export/replay growth and theorem coverage. E4. |
| E5 | Overstatements or missing caveats in e1.md / contract Status; replacement text | overstated | Material repairs: causal order wording, reuse universals, M3 closure/outlier inference, RSS units, baseline subtraction, snapshot/measurement boundary, static-node denominator and inventory over-certification. None reverses the partial-close / no-route-winner ruling. | Paste replacements in E5. Preserve measured historical numbers as historical; use the narrower supported result rather than rerunning until a preferred ranking appears. |
| E6 | Reruns needed before shipping the numbers | open | Archived M1/M2 arithmetic and exported axiom/root records check out. The post-measurement O1/Common extraction is now disclosed in e1.md. Historical results can ship after corrections; final-source acceptance and any final-state performance claim need matching evidence. | No new timing campaign is required for the inconclusive ruling. Recheck the changed final proof closure before calling current artifacts accepted; regenerate counts/timings only if replacing the historical snapshot with final-state numbers. E6. |

## Scope + evidence pins

Recommendation: **accept the bounded checkpoint-1 result and the partial close; revise the stronger causal/scaling wording.** Both methods constructed an all-input lemma for one literal-length loop and its optimizer-perturbed counterpart. This is meaningful proof feasibility at that scope. It is neither a completed decoder verification nor evidence that one route is generally more scalable.

Root = `/home/eturkes/Projects/fva/`. Inspected result snapshot: `.scratch/u19/e1.md` sha256 `e830aecefab7bcc696f68d0ee08ea8eee25aa2e6f29f976765539c45892c9b88`; contract `4e4024b6aa1cbab5ddb62b4fe985f4f7fcbe2631576a6fd46f763ceffd00b208`. The pre-refactor disclosure was present when this hash was pinned. Frozen statements match the reported hashes: `Ext.lean` = `3466d1aa31b665958369fcdfdb60b2e8377be1461b81411a4e288d76acff7387`; `O1/Ext.lean` = `aefcd9ddd5499a0b6290e87dbc66a131553bf4d5683b5155152cde3295b19123`.

Read: both statement files; all four route proof files; shared O1 helper file; Code slices; route log; measurement scripts, baselines and raw timing logs; all 109 M1 index/count rows; selected declaration snapshots; archived exports through bounded record extraction. No builds, compiler runs, Lean elaboration, kernel replay, full gate or external-source retrieval performed. Recorded checker rc=0 is evidence from MAIN's runs; this appraisal independently checked record content, not checker execution.

## E1 — protocol ruling + confounding

**Eligibility:** all four source roots have the intended statement type (`ExtL1` for D/R, `ExtL1O1` for O1 D/R). Textual export audit P3 finds exactly the expected `ext_l1` root in each archived closure and exactly three axiom records: `propext`, `Quot.sound`, `Classical.choice`. Export metadata agree on Lean 4.35.0, git hash `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, exporter 3.1.0. Raw M3 log records acceptance by both default checkers for every historical export. This supports the frozen checkpoint-1 acceptance target; it is not `fva trust` PASS for decoder R1–R3, nor a new replay of current refactored sources.

**Decision rule:** raw construction intervals favor R; repair intervals favor D. Neither route dominates even before timing uncertainty. Recomputed M2 ranges are O2 D `[10.38,15.97]`, R `[10.38,14.62]`; O1 D `[17.75,19.73]`, R `[14.44,18.00]` seconds. Neither direction satisfies `min(slower) ≥ 2×max(faster)`. M3 has one observation per route/checker, so it supplies acceptance and descriptive costs, not a repeated-measure timing ranking. The frozen rule therefore yields inconclusive → D provisionally, as reported. “No detected 2× separation” is not equivalence or proof that smaller differences do not exist.

**Order:** logs explicitly say R reused D's O2 stepping script; D reused R's O1 script and tactic. Common arithmetic helpers were first authored in D's interval. Reversing order for repair reveals the consistent second-implementation advantage, but repair is a different task and code shape. Learning, copied artifacts, easier second-task adaptation and true route differences remain inseparable. The observation supports a serious carryover confound, not its quantified dominance. There is no independent author/loop/compiler-transition replication; timing repeats do not add such replication.

**M0 precision:** endpoint subtraction gives D 1,290 s = 21.50 min; R 273 s = 4.55 min; O1 shared 160 s = 2.667 min; R repair 442 s = 7.367 min; D repair 192 s = 3.20 min. These are contiguous authoring-to-proof intervals, not instrumented active-agent work. The subsequent measurement/export/replay campaign is outside those intervals. Label the boundary; avoid interpreting them as total proof-delivery or fvapi request cost.

## E2 — what the line counts establish

P1 recomputes totals from every `index.json` / `counts.tsv` row: common 32, D 281, R 313, O1 binding 67, O1 D 251, O1 R 267. No missing count row: expected 109, observed 109 in both inputs. These are **historical pre-refactor counts**; current O1 files were shortened by shared-helper extraction.

The published bins are not symmetric: D's `ext_l1` wrapper is counted as stepping, while R's corresponding wrapper is counted as composition. D's invariant/frame helpers are called “spec reasoning”, while R's corresponding state relation is binding. A sensible sensitivity check counts only `one_iter + iter` or `sim_one + sim` as machine-facing segment/induction work:

| version | D | R |
|---|---:|---:|
| O2 | 210 / 281 = 74.73% | 191 / 313 = 61.02% |
| O1 | 191 / 251 = 76.10% | 170 / 267 = 63.67% |

The majority finding survives that correction. But each large lemma contains semantic stepping, guard arithmetic, locals updates, frame equalities, invariant preservation and exit packaging. It is not a time profile of `wasm_cstepu` or kernel normalization. “Machine-facing proof source accounts for most route-specific lines” is supported; “stepping is the dominant runtime/engineering cost” remains unmeasured.

**Reuse:** R's O1 file imports `ExtRefine` and calls the unchanged `extModel` / `model_ok`; its 68-line model package is reusable. O1 D imports `ExtDirect` and uses `run`, `psum_eq`, `run_succ`, `run_zero` (7 archived code lines), alongside the common helpers used by both routes. R's 59 lines of new binding/composition are real, but comparing 59 written lines to 68 retained lines cannot identify a counterfactual saving or offset: D has its own binding/invariant work, reused lines are not development minutes, and the source partition is implementation-dependent.

Rival explanation: the tiny declarative property is cheap enough that model abstraction has little to amortize, whereas a rich full-decoder semantic theorem could reuse much more. Rival: the simulation was handwritten at instruction granularity, so both routes inherited that bottleneck. Separating observation: reuse the same richer model/property on a second substantial code region or compilation while independently recording simulation, semantic theorem and composition effort. The present result does not falsify refinement or establish an automatic decompiler as the required next architecture.

## E3 — perturbation validity + economics

The intervention is meaningful: O2/O1 literal-extension bodies have 22/33 static instruction nodes, with changed locals, address arithmetic and exit control. The frozen byte/partial-sum facts and successful-access bounds are retained in build-specific statements. O1 additionally states the larger locals-list size needed by its physical layout; its error cutpoint stops before the enclosing error-path code. These are concrete rebinding choices, not proof that whole-program observations of the two builds are equivalent. Both routes face the SAME statement within each build, so this is not an arm faithfulness mismatch.

Supported result: both repair attempts succeeded for this optimizer perturbation, using new version-specific machine-facing proofs and some unchanged logical material. What is not identified:
- cost distribution over source releases, compiler versions, target features or changed requirements;
- irreducible amount of new stepping proof (the author chose an additive new-version repair strategy rather than benchmarking maximal reuse);
- amortized cost or business feasibility for fvapi;
- end-to-end verification latency from a fresh artifact with no prebuilt dependencies.

“No O2 proof line changed; deleted 0” is true by the chosen **add-a-new-version-module** organization. It is not an edit-distance result between equivalent in-place maintenance strategies. Call the 251/267 lines newly added version-proof source, not a method-independent minimal repair delta. The shared 67-line binding and 160-second interval remain separate; include them in any complete transition cost. The actual source-release/compiler-version transition stays out of scope, as the contract correctly states.

Knowledge fit: the prior-art evidence already gathered supports the possibility that optimized control-flow changes alter proof cutpoints; it did not establish that every instruction lemma must be discarded. Researcher-1 A2 quotes the proof-producing decompiler's reusable certificate relation, while A3's optimizer comparison is system-specific. This observation is another local case, not a universal negative result about binary-proof reuse.

## E4 — checkpoint-2 readiness + highest-value next work

The frozen gate is conjunctive: every remaining class must have a demonstrated pattern, plus a conservative session allowance. I4–I9 plainly fail the first requirement; no time extrapolation is needed to decline checkpoint 2. Correct status = “checkpoint 1 complete; checkpoint 2 not attempted; U19 partial.” Not “decoder infeasible”, “full theorem failed”, or “requires more than a session”. The longer phase is a routing recommendation subject to the user's ruling, not a scientific consequence that overrides that decision.

Inventory precision:
- I1: generic straight-line/footprint machinery exists; the decoder entry/zero-capacity path has not been proved by the two L1s.
- I2: **literal-length extension** proved. Applying it to match-length extension is a proposed transfer, not a theorem established by either current root.
- I3: a loop that reads and updates an evolving memory needs store/frame/overlap reasoning not exercised by read-only L1. Mark candidate pattern / untested transfer. The ≤2 real-path bound itself belongs in the full invariant.
- I10: induction on a decreasing measure is established; monotonic `ip`, all main-loop paths and negative-return arithmetic remain decoder-specific obligations.
- I7 “dominant” = informed hypothesis about the largest unresolved semantic obligation, not measured dominance.

Recommended first IMPLEMENT measurement, ranked by information value:
1. **I4 vertical slice:** one all-input copy-summary theorem with successful-access footprint, then one actual caller composition. Record first-summary effort vs a second call-site instantiation, new/reused LOC, peak resources, export size and replay cost. Keep `memcpy` and `memmove` semantics distinct: this shim's `memcpy` copies forward and can repeat bytes under overlap; `memmove` selects direction and preserves the original source bytes. P4 exhibits the difference. A single undifferentiated “sequential-copy result on overlap” contract is too vague.
2. **I7 semantic seam, early:** one complete decoder sequence (including a shortcut/bound case), conditional on explicitly stated callee contracts, with a kernel-checked connection to the existing LZ4 format vocabulary. Measure semantic invariant design/composition independently of instruction stepping. Conditional helper correctness is useful evidence but not the final decoder theorem. This tests the highest-risk claim before building an entire automation layer.
3. **Reuse experiment:** only after a substantial semantic property exists, perturb a second artifact and log the invalidated interfaces: extraction/binding, segment summaries, main invariant/model theorem, spec. Match authoring budgets and record carryover. This distinguishes proof reuse from merely replaying a stored proof.

## E5 — replacement wording / caveat register

Paths/anchors below refer to the pinned snapshots; quotes are verbatim excerpts from the inspected files.

| finding | anchor / original | replacement |
|---|---|---|
| F1 | `e1.md:59`: “order effect dominates the signal” | “The second implementation was quicker in both phases, with documented copying of the earlier script. Route and carryover effects cannot be separated in this case study.” |
| F2 | `e1.md:64`: “Stepping dominates both routes” | “Machine-facing iteration/induction proofs account for most route-specific source lines under either the original bins or symmetric grouping. Their share of authoring time and runtime was not measured.” |
| F3 | `e1.md:64`: “saved its 68 lines … cost about as much → … a full re-step either way” | “R reused its 68-line model package and added 59 lines of binding/composition plus a new machine-facing proof. D also reused logical helpers. Both chosen repairs added substantial machine-facing proof; no minimal-repair or causal cost-offset estimate was made.” |
| F4 | `e1.md:65`: “a per-instruction proof never survives it; only the declarative statement and (R) the model do” | “This transition changed the loop's control structure and locals enough that both implementations supplied new version-specific iteration proofs. The byte-level property, common semantic/arithmetic lemmas, D's sum helpers and R's model theorem were reused.” |
| F5 | `e1.md:52`: “the closure … dominates, not the route” | “Total export sizes differ by 0.247% at O2 and 0.223% at O1. Shared declarations likely explain much of the size, but their exact contribution was not measured.” The statement-only export is 36.74% of D's bytes; similar total sizes alone do not identify the remaining shared fraction. |
| F6 | `e1.md:52`: “one outlier … 93 s” | “The largest single con-leche observation was 92.96 s for O1 R. No repeated distribution was measured, so its cause and repeatability are undetermined.” Keep every observation. |
| F7 | `e1.md:35–51`: RSS values labelled GB from `%M` | “RSS in KiB (GNU time `%M` on Linux), optionally converted to GiB by dividing by 1,048,576.” M2 maxima: D 2.599 GiB, R 2.609 GiB, O1 D 2.627 GiB, O1 R 2.622 GiB. Multiplying raw KiB by 1,024 gives bytes; dividing the raw number by 1,000,000 is not GB. Apply the same correction to M3. |
| F8 | `e1.md:36`: “baseline … no proofs”; “net median” | “Import-only baseline (dependencies already compiled, including prior route modules for O1); difference of medians, descriptive only.” This is neither median paired difference nor isolated proof-elaboration time. P2 gives the alternative paired summaries; neither changes the ruling. |
| F9 | `e1.md:13–21` M0/M4 | “Elapsed authoring-to-first-proof intervals, including in-interval waits; later measurement/export/replay excluded. R's initial interval = 273 s = 4.55 min.” Do not present these as end-to-end verified-update latency. |
| F10 | `e1.md:35/44` timing boundaries | “M2 = route-source elaboration with prebuilt imports, not a clean dependency rebuild. M3 = single historical export/replay observations; the script pins checker processes to CPU 3, while exporter affinity is not recorded by that script.” `m3/run.sh:11` has no `taskset`; line15 pins checkers. If launch affinity was set externally, record it instead. |
| F11 | `e1.md:55`: “22/33 instructions/iteration” | “22/33 static instruction nodes in the loop bodies; early exits and O1's exit-only branch make dynamic path counts differ. No per-semantic-step timing was measured.” `routes.md`'s earlier “30” should be explicitly superseded by the 33-node count, not left as an apparent competing measurement. |
| F12 | contract `Status:51`, “every theorem … all exports accepted” | “The four historical checkpoint-1 exports contain only the standard axioms and were accepted by the two default checkers. Metrics precede the shared-helper extraction; final-source acceptance is recorded separately.” Keep checkpoint 2 explicitly not attempted. |
| F13 | contract inventory I1/I2/I3/I10 | Use the narrower statuses in E4: generic machinery available / literal extension proved / remaining target-specific transfers untested. The gate remains unmet. |
| F14 | contract inventory I4 | “Separate actual ordered-copy contracts for the compiled memcpy and memmove shims, with bounds, framing, termination and call composition; do not equate forward-overlap repetition with memmove's source-preserving result.” |
| F15 | contract Purpose: “no LZ4 decoder proof exists”; “no controlled … comparison exists” (outside Status, but visible nearby) | “The cited survey found no completed matching LZ4 decoder proof or controlled direct-vs-refinement comparison in the sources inspected.” A bounded survey cannot establish global nonexistence. |

The new snapshot note in `e1.md:3` already repairs the immediate source/measurement mismatch. Three pairs of archived helper declarations compare byte-identical: `c083/c097`, `c084/c098`, `c087/c103` (all `cmp` rc 0). This supports their shared extraction, not the broader claim that every proof file is byte-identical after imports/names change. Current O1 D/R contain 243/261 physical lines, so the historical 251/267 code-line totals must retain their explicit snapshot label.

## E6 — what must rerun, and what need not

**Before publishing the historical case-study numbers:** correct units/labels, preserve the raw logs and declaration snapshots with input hashes, and scope acceptance to the recorded exports. Recomputed counts/medians/range tests do not require another timing campaign. The lack of a route winner is robust to these corrections. Three more noisy timing runs would not remove authoring carryover or answer full-decoder feasibility.

**Before claiming the current refactored proofs accepted:** MAIN must build/export/replay the changed closure under the same default acceptance set, unless matching final-state evidence already exists elsewhere. I did not run or locate a final-state route replay in the provided M3 logs; their exports predate the O1/Common extraction. This is normal final-artifact verification, not a new benchmark metric or a new acceptance threshold.

**Only if publishing final-state performance/LOC instead of historical numbers:** regenerate M1 and rerun the affected M2/M3 measurements on a frozen manifest (source hashes, import/dependency hashes, Lean/exporter/checker binaries, commands/affinity/limits). Do not blend historical authoring intervals with a relabelled final implementation. The existing scripts append logs; a new campaign needs distinct run ids/files and source pins rather than concatenating results without boundaries.

**Optional, decision-dependent:** repeated paired M3 checks are needed only if a replay-speed ranking or a resource-limit claim will steer the architecture. Use fixed exports and balanced order; include export costs separately. A genuine compiler/source-release transition is needed before any version-economics conclusion. Neither is needed to close this spike partial.

## P1 — raw M1 recomputation + category sensitivity

Commands:
```bash
jq 'length' /home/eturkes/Projects/fva/.scratch/u19/m1/index.json
awk 'END {print NR}' /home/eturkes/Projects/fva/.scratch/u19/m1/counts.tsv
jq -r '.[] | [.i,.file,.name] | @tsv' /home/eturkes/Projects/fva/.scratch/u19/m1/index.json |
  awk 'NR==FNR {c[$1]=$2; next} {n[$2]+=c[$1]; if ($3=="one_iter" || $3=="iter" || $3=="sim_one" || $3=="sim") step[$2]+=c[$1]} END {for(f in n) printf "%s total=%d segment_plus_induction=%d pct=%.2f\n",f,n[f],step[f],100*step[f]/n[f]}' /home/eturkes/Projects/fva/.scratch/u19/m1/counts.tsv - | sort
```
Positive controls expected 109 entries/counts; output:
```text
109
109
common total=32 segment_plus_induction=0 pct=0.00
D total=281 segment_plus_induction=210 pct=74.73
O1bind total=67 segment_plus_induction=0 pct=0.00
O1D total=251 segment_plus_induction=191 pct=76.10
O1R total=267 segment_plus_induction=170 pct=63.67
R total=313 segment_plus_induction=191 pct=61.02
M1_recompute_rc=0
```
Coverage: every indexed count; no rerun of `FVA.Trust.codeLines` (that would require a Lean invocation, prohibited by this brief). Classification sensitivity uses complete named declarations, not a time profile.

## P2 — timing recomputation + subtraction sensitivity

Command (the executed corrected awk; `median_round_difference` pairs each route with its same-round import baseline):
```bash
awk '$1 ~ /^[123]$/ {split($3,t,"="); split($4,rr,"="); v[$2,$1]=t[2]; if(rr[2]>rss[$2])rss[$2]=rr[2]} function median(a,b,c, t) {if(a>b){t=a;a=b;b=t} if(b>c){t=b;b=c;c=t} if(a>b){t=a;a=b;b=t} return b} END {a[1]="D";a[2]="R";a[3]="O1D";a[4]="O1R";b[1]="B1";b[2]="B1";b[3]="B2";b[4]="B3";for(i=1;i<=4;i++){route=a[i];base=b[i];printf "%s rawmedian=%.2f diff_of_medians=%.2f median_round_difference=%.2f maxRSS_KiB=%d GiB=%.3f decimalGB=%.3f\n",route,median(v[route,1],v[route,2],v[route,3]),median(v[route,1],v[route,2],v[route,3])-median(v[base,1],v[base,2],v[base,3]),median(v[route,1]-v[base,1],v[route,2]-v[base,2],v[route,3]-v[base,3]),rss[route],rss[route]/1048576,rss[route]*1024/1000000000}}' /home/eturkes/Projects/fva/.scratch/u19/m2/times.log
```
Positive control: 21 measured observations, all 21 rc=0 (warm-ups excluded). Output:
```text
D rawmedian=10.41 diff_of_medians=7.05 median_round_difference=7.31 maxRSS_KiB=2725080 GiB=2.599 decimalGB=2.790
R rawmedian=11.40 diff_of_medians=8.04 median_round_difference=8.30 maxRSS_KiB=2735988 GiB=2.609 decimalGB=2.802
O1D rawmedian=17.98 diff_of_medians=14.59 median_round_difference=14.54 maxRSS_KiB=2754792 GiB=2.627 decimalGB=2.821
O1R rawmedian=15.69 diff_of_medians=11.08 median_round_difference=11.36 maxRSS_KiB=2748980 GiB=2.622 decimalGB=2.815
M2_recompute_rc=0
```
Separate min/max recomputation: O2 D `[10.38,15.97]`, R `[10.38,14.62]`; O1 D `[17.75,19.73]`, R `[14.44,18.00]`; both directions' 2× tests = false for both versions, rc 0. No outlier removal or additional sampling.

Initial recomputation attempt used `r` as both an awk array and scalar: `fatal: attempt to use array 'r' in a scalar context`, rc 2. Corrected version above alone supplies results.

## P3 — archived export sanity audit (not a kernel replay)

Command:
```bash
set -o pipefail
for tag in D R O1D O1R; do
  printf '%s\n' "$tag"
  rg '^\{"in":|^\{"axiom":|^\{"thm":' "/home/eturkes/Projects/fva/.scratch/u19/m3/$tag.export" |
    awk 'match($0, /^\{"in":([0-9]+),"str":\{"pre":([0-9]+),"str":"([^"\\]*)"\}\}$/, a) {n[a[1]]=(a[2]==0 ? "" : n[a[2]] ".") a[3]; next} /^\{"axiom":/ && match($0,/"name":([0-9]+)/,a) {print "axiom=" n[a[1]]; ax++} /^\{"thm":/ && match($0,/"name":([0-9]+)/,a) {if(n[a[1]] ~ /\.ext_l1$/) {print "root=" n[a[1]]; roots++}} END {printf "axiom_count=%d expected=3 root_count=%d expected=1\n",ax,roots; exit !(ax==3 && roots==1)}'
  rc=$?; printf 'bounded_export_audit_rc=%d\n' "$rc"
done
```
Each output: `axiom=propext`, `axiom=Quot.sound`, `axiom=Classical.choice`; count 3; expected matching root count 1; rc 0. Roots respectively `Subjects.Lz4C.Direct.ext_l1`, `Subjects.Lz4C.Refine.ext_l1`, `Subjects.Lz4C.O1.Direct.ext_l1`, `Subjects.Lz4C.O1.Refine.ext_l1`.

Limit: record-format audit, not trusted proof checking, source-to-export correspondence, or declaration reachability recomputation. Name parsing covers ordinary string-name entries needed by these recorded names; no general parser correctness claim. An initial generic jq accumulation was stopped after exceeding the 120-second foreground limit; it produced no audit result. The bounded streaming extraction above replaced it and completed. No checker was rerun.

M3 size arithmetic from `times.log`: O2 R−D = 302,466 bytes (0.2468% of D); O1 R−D = 273,958 bytes (0.2227% of O1 D); statement-only BASE / D = 36.74%, rc 0. This confirms close total sizes, not a measured shared-closure decomposition.

## P4 — overlap semantics check for I4

Source anchors: `bench/subjects/c-memory.c:3–7` forward memcpy; `:10–18` direction-selecting memmove. Discriminating example: bytes `abcde`, source 0, destination 1, length 3.
```bash
awk 'BEGIN {for(i=0;i<5;i++){f[i]=sprintf("%c",97+i);b[i]=f[i]} for(i=0;i<3;i++)f[1+i]=f[i]; for(i=2;i>=0;i--)b[1+i]=b[i]; printf "forward=";for(i=0;i<5;i++)printf "%s",f[i];printf " reverse=";for(i=0;i<5;i++)printf "%s",b[i];printf " expected=aaaae,aabce\n"}'
```
Output `forward=aaaae reverse=aabce expected=aaaae,aabce`, rc 0. This checks the ordered-update distinction, not the compiled shims or their full-domain correctness.

## Implications

- A real compiled guarded loop is now amenable to both proof organizations, with successful-access tracking and two build layouts. This narrows one feasibility gap without closing the decoder gap.
- The strongest scaling lead is **machine-facing proof factoring and reusable call summaries**, not a demonstrated victory of D or defeat of R. Test it at the next semantic/call boundary before committing to a large automation rewrite.
- The strongest version-proof result is **some logical material survives while machine-specific binding changes**. “Cheap next release” remains open; delivery/checking costs and requirement changes matter as much as retained source lines.
- No additional benchmark is needed to justify the present partial close. Final-artifact checks and honest scope labels are the remaining shipping requirements for these results.

scientist-1-E1-DONE
