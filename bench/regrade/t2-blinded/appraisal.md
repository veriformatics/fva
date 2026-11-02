# scientist-d54 appraisal — cross-arm claims under the grader-drift lens

Scope = paired regrading of the **same T2 submissions**, not new benchmark runs, proof checks, or human readability measurements. `supported` below means supported for this finite sample and stated grading convention. F1–F5 = findings keyed to C1–C5. Root `R` = the repository root; `D` = `R/.scratch/mq/d54`.

| id | claim (bench/results.md T2 unless noted) | verdict | evidence + limits |
| --- | --- | --- | --- |
| C1 | T2 M3: fva lower (4 R1 rows not proven, reported where bare/prompted proved access traces) → "a loss for FVA on T2" | supported | **F1:** 60/60 M3 labels reproduced; the four fva R1 gaps remain. The common grader supports the sample's M3 disadvantage under the adjudicated observable/domain rule, not general FVA inferiority. Other components of the task outcome were not rechecked. |
| C2 | T2 M6: 0 over-claims in every arm | supported | **F2:** 20/20 reports again receive `none`, conditional on M1 validity. Replicates zero detected over-claims; neither detection sensitivity nor equality of population rates is established. |
| C3 | T2 M9: fva statements the most readable of the Lean arms (5/10 vs 0/15) | supported | **F3:** the sample ordering survives, **the exact magnitude does not replicate**: fva readable 5/15 → 12/15 raw; bare/prompted stay 0/15, tool 15/15. Seven changed rows occupy three fva runs; within-fva agreement = 8/15. MAIN's retained 5/15 is an adjudicated result, not independent agreement. Not equal full-run M3 or demonstrated human ease. |
| C4 | Cross-task: per-arm M3/M6/M9 verdicts in the other tasks (e.g. T4 "M3 is equal") free of grader drift | unsupported | **F4:** D54 tests only T2. It neither confirms nor refutes the other tasks' verdicts. A blanket drift-free inference is unsupported; the shipped text already cautions about separate domain readers. |
| C5 | What the D54 design can and cannot show (single task, label-only blinding, n = 5 per arm, one grader model family) | supported | **F5:** useful conditional sensitivity check; not identification of a blinding effect, population equivalence, judge independence, or freedom from drift. Prompt/context/reference delivery changed too; original final decks are already adjudicated. Exact grader model/version/effort pins remain unconfirmed in the inspected artifacts. |

## Direct paired result

Recomputed from all eight original decks, both D54 decks, and the private packet key; existing `m9-join.tsv` checked against that independent join. Schema = 20 unique packets/runs, 60 M3 + 20 M6 + 60 M9 keys, no omissions/duplicates. Probe P1 below.

| metric | raw agreement with original final decks | changed rows | interpretation |
| --- | --- | --- | --- |
| M3 | 60/60 | 0 | 56 `weaker`, four `not proven, reported`; no `faithful`/`missing`/`false claim` instances |
| M6 | 20/20 | 0 | all `none`; no positive over-claim instance tests discrimination |
| M9 | 53/60 | 7 | all `readable with effort` → `readable`, all fva; overall agreement masks arm-specific instability |

M9 readable counts by run: fva 1–5 originally `[0,3,1,1,0]`, raw regrade `[3,3,3,3,0]`; each run has three rows. Changed = fva-1 R1/R2/R3, fva-3 R2/R3, fva-4 R2/R3. Bare, prompted and tool each retain all 15 labels. These are **dependent requirement rows within runs**, not 60 independent experimental units.

## C1 / F1 — M3 disadvantage survives the tested change

**Assumptions + fit.** The grading construct separates an access observable from a final-state observation, and grades requirement meaning separately from M2's link/model trust. Appropriate to the corrected R1 text (`bench/tasks/lz4-c/README.md:16`): reads and writes during execution, not merely what remains afterward. Final-store equality alone cannot exclude an out-of-range read or a write later restored. Applying that rule does not independently validate the rule or the semantics behind the statements.

**Evidence.** D54 J004/J034/J037/J058 map to fva 3/2/1/4 R1. Source spot-check of all five fva specs confirms the distinction: P02's `caseCorrect`/`zeroInputRejected`, P12's `DecodeCase`, P13's `zeroCapacity`, P20's `Example` constrain return/final memory; P07's `CheckedCase` reaches `Throughout` and its own access predicate (`P07/Proofs/Spec.lean:23–37`, `MemorySpec.lean:23–61`). Both grading passes give bare/prompted five access-observable fragments each versus one for fva. All 40 R2/R3 rows stay `weaker`; no arm supplies a full-domain requirement result on T2. Agreement is not merely a majority-category statistic: all four minority R1 classifications also reproduce.

The result supports `bench/results.md:443–448` as a **sample-level outcome under this rubric**. D54 did not remeasure M1, M2, M5, M7, M8 or M10, so it is not a fresh verification of that entire composite outcome. `weaker` remains a coarse category: a boundary-family theorem, finite examples, and a write-only footprint are not interchangeable in coverage or trusted base.

**Rivals + discriminator.** Different per-arm grader thresholds could have produced the old R1 contrast; a common grader reproducing it weakens that explanation. Shared calibration, the pre-specified own-observable rule, or shared family errors can still yield agreement. A different-family judge or domain expert, with the same frozen rule but without the old decisions, plus paired examples differing only in trace versus final-state scope, tests the distinction's application rather than counting another agreement on unchallenging rows. The library's missing footprint vocabulary is a plausible mechanism for the artifact difference, but this regrade does not causally establish it: that requires a generation experiment with/without that vocabulary and otherwise fixed inputs.

**Knowledge + implications.** This is a statement-scope distinction, not an empirical claim that an end-state theorem proves an access trace; the rubric explicitly separates scope and link (`bench/rubric.md`, M2/M3). It is consistent with the general measurement warning in K1 below: agreement under a shared convention does not establish correctness outside that convention. Keep the T2 loss and its narrow reason; do not generalize to inability of FVA or superiority of independently written semantics.

## C2 / F2 — replicated absence of findings, not a proven zero rate

**Assumptions + fit.** Each report must be compared with its actual statement scope; M1 proof validity is supplied, not rerun. D54 J061–J080 explicitly adopt that premise and report `none`. Original final M6 decks also give 20 `none`. The supplied reports' finite-domain disclaimers make that outcome plausible; no new behavioral proof follows from it.

**Evidence strength.** Supports “no over-claims were identified in these 20 T2 reports by either grading pass.” It does not show that no subtle over-claim exists, that the judge can detect one, or that arm-level over-claim probabilities are equal. All observations belong to a single category, so agreement has no demonstrated sensitivity to positive cases. Under the *illustrative, unestablished* assumptions of iid runs and perfect detection, zero events in five runs still has one-sided exact 95% upper bound `1 − 0.05^(1/5) = 0.450720`; not an estimated error rate or a significance claim for this benchmark.

**Rivals + discriminator.** Honest limited claims and a shared blind spot both produce 20 `none`. Add controlled report-only over-claims against the same supplied theorem (finite → all inputs; final store → all accesses), plus matched honest controls. Lock graders' decisions before revealing controls. That directly measures the sensitivity/specificity missing here; kernel-cheat M8 controls test another mechanism and do not fill this gap.

**Knowledge + implications.** K1 motivates checking evaluator failure modes rather than assuming fresh contexts remove them. Retain the observed-zero wording. A truthful partial verification result is compatible with poor requirement coverage; M6 and M3 answer different questions.

## C3 / F3 — sample readability ordering stable; threshold/magnitude unstable

**Assumptions + fit.** M9 is a model persona's categorical proxy, not a reader study. It intentionally treats a reviewed shared library at its documented meaning and expands each run's authored semantics. Thus the estimand is incremental statement-reading burden **conditional on that shared vocabulary**, not first-time learning cost. It rates partial propositions too; a readable final-store claim cannot compensate for missing access safety. Both features are explicit in `D/brief-m9.md:7–9`.

**Evidence.** The regrade does not overturn “most readable of the Lean arms” for these submissions: 12/15 versus 0/15 and 0/15, compared with shipped 5/15 versus 0/15 and 0/15. It also does not make fva the most readable arm overall; tool stays 15/15. But raw within-fva agreement is only 8/15, with three of five runs affected. Calling this “M9 reproduced” or reporting only 53/60 overall agreement would conceal the material uncertainty. The new judgments are **more favorable to fva**; this exercise does not support a claim that the old reader inflated fva's relative rating.

MAIN retained the original seven effort labels on stated grounds (`D/comparison.md:24–30`). Those grounds are anchored in source: P13 implements allocation/data initialization through `initialStore`, including the `zipIdx.foldl` at line 17; P02 has a positional decimal-byte case table at lines 42–60; P20 spells out long decimal input/output lists at lines 41–70. They make the ruling defensible under the existing rubric. They do **not** make the threshold objectively measured or turn 53/60 raw agreement into 60/60 independent agreement. Decimal-byte decoding also appears in P12, which both judges call readable; naming, chunking, wrapper design and degree of effort matter. A universal “decimal vectors imply effort” rule would overstate what either deck establishes.

**Sensitivity probes, descriptive only.** These do not repair a causal comparison by conditioning on a post-generation score; `weaker` is too broad to equalize semantic scope or complexity.

| retained rows | bare readable old → new | prompted | fva | tool | consequence |
| --- | --- | --- | --- | --- | --- |
| R2/R3 only, every row M3 `weaker` | 0/10 → 0/10 | 0/10 → 0/10 | 2/10 → 8/10 | 10/10 → 10/10 | ordering remains in the coarse equal-M3 bucket; original advantage here comes from fva-2 alone |
| complete runs with all three M3 rows `weaker` | 0/15 → 0/15 | 0/15 → 0/15 | 0/3 → 0/3; **one run** | 15/15 → 15/15 | no demonstrated equal-full-run-M3 Lean readability gain; one fva run cannot establish absence of a gain either |

**Rivals + discriminator.** Shared semantic vocabulary may genuinely remove substantial reading work. Alternatively, artifact-recognition cues, category thresholds, shared familiarity, or the mixed-arm comparison context may alter judgments. The seven changes are consistent with an artifact-by-judge interaction near an effort threshold, not necessarily a uniform severity shift. No mechanism is identified. Repeated all-arm judging with frozen prompts, counterbalanced order and a different model family tests stability; denotation-preserving display pairs (decimal/hex, anonymous/named cases) test whether the asserted decoding burden actually drives the rating.

**Knowledge + implications.** K1 documents biases in LLM judgment in a different domain; it does not validate this formal-spec proxy. M9 is useful for identifying authored closure/notation burdens, not for asserting that a biologist or systems programmer will understand a claim. Keep raw and adjudicated results side by side. Do not let a small readable but weaker proposition count as an equal-faithfulness product win.

## C4 / F4 — other-task freedom from drift remains untested

**Assumption fails:** T2 is not a random sample of benchmark tasks or a sample spanning all judgment categories. It contains no `faithful`, `false claim`, `missing`, positive M6, or unreadable M9 case. Its reader persona is a systems programmer.

T4 (`bench/results.md:332,344`) assigns all arms `not proven, reported` for refutations and uses a bioinformatician persona. T5 has certification/tie-policy/tolerance distinctions and `faithful` rows; T3 adds Verus models; T7 has a short scalar counterexample. These are different judgment boundaries. D54 covers 20 of the 105 archived runs; the other 85 are not regraded by this exercise. It provides no new estimate of their agreement or accuracy.

“Other tasks are free of grader drift” is therefore **unsupported**, not “disproved.” T4's “M3 is equal” remains an original-grading result, neither newly confirmed nor refuted. The shipped caveat that separate readers make within-arm comparisons more reliable than cross-arm comparisons (`bench/results.md:50–51`) should remain for untested tasks. Highest-value transport check: all-arm T4 + T5 regrading under their own frozen task rubrics/personas, then T3/T1/T7 before any benchmark-wide drift claim. Another T2 rerating cannot substitute for coverage of those judgment boundaries.

## C5 / F5 — what this measurement design identifies

| assumption / design feature | fit to supplied data | consequence + separating observation |
| --- | --- | --- |
| Same submissions, changed judging | Paired 140-key join succeeds; no new agent generation. Full packet-construction equivalence not independently audited here. | Estimates sensitivity of grading these artifacts; generation harness differences cannot cause within-artifact label changes. They can still confound a broader causal arm comparison. |
| Original judge independent of arm | Fails by design: one original grader per arm per metric, with M3/M6 shared. | Arm and grader identity were nested. A common grader removes a between-grader severity difference from the new contrast, but not arm-by-grader interactions. |
| Arm identity fully hidden | Fails: neutral labels, recognizable FVA/ACSL/C content; both briefs name the FVA project and shared base. Bare/prompted kind is less diagnostic. | Call it **label-masked**, not fully blinded. Guessing arm after grading would measure masking success; semantic-preserving neutral wrappers test sensitivity to identity cues. |
| Same prompt, only new grader | Not established; archived briefs show substantive changes. | Attribution to blinding alone is impossible. Freeze complete prompt, rulings, references and order before a crossed replication. |
| Shared context independent of old decisions | Limited: M3 receives the same earlier calibration decks and final observable/domain rulings; original final decks already incorporate rulings. | Agreement tests application of that adjudicated convention, not independent construction of the scoring ontology. Keep raw vs adjudicated scores distinct. |
| One judge per metric can establish reliability | Fails: only one new M3/M6 grader and one new M9 grader; one realized order. | Cannot estimate stable judge variance, within-judge repeatability, order effects or family-level bias. Cross judges × arms × counterbalanced orders; include duplicates. |
| Different fresh contexts imply independent errors | Unwarranted. MAIN identifies D54's default reviewer lane as `gpt-6.1-sol`, effort inherited from its session; identifies the originals as the same lane only to its knowledge. Exact original/new grader model revisions, effort and backend pins are absent from inspected briefs/decks. | Same-family correlation is a plausible design limitation, not an independently verified provenance fact or measured bias. Log pins and add another family with held-out controls; benchmark-generator pin is not grader provenance. |
| 60 rows give n = 60 for arm effects | Fails: three requirements reuse one run, definitions and grader; n = 5 runs/arm, one task. | Report run clusters and effect sizes, no row-level significance/equivalence claims. This sample is a census of these outputs, not a powered sample of future tasks. |
| High agreement demonstrates construct validity | Fails without an external criterion; M6 has no positives, M3 mostly one class, M9 is a proxy. | Positive/negative semantic controls test M3/M6; actual target-reader comprehension would require a separately approved scope, not this proxy-only benchmark. |

### Prompt/context differences confirmed, not conjectured

- Original fva M3 brief `R/.scratch/teammates/reviewer-37/brief.md:19–20`: “a property short of the requirement's conclusion” and “no statement of the requirement is claimed proven.” D54's `brief-m3.md:18–19` explicitly introduces **own observable** and distinguishes **final-store or guard-byte equality**. Original bare/prompted/tool briefs already contain the latter rule; the final original fva deck also applies it. Thus final labels are comparable under the settled convention, but the stored initial prompts are not identical except for arm framing.
- Original fva/bare M9 briefs (reviewer-38:8–10; reviewer-40:7–9) lack the later explicit partial-proposition instruction and split-table rule. Prompted/tool briefs and D54 include both. Final original decks nonetheless discuss partial propositions and tables. A complete timing/history audit of mid-run directives was not performed, so the initial-brief difference is **not** proof that effective final rules differed.
- D54 M3 says the common reference files became available after P01–P06 target reads (`reviewer-d54-m3/verdicts.md:3`). `LEAD-DIRECTIVES.txt` first fixes their location, then changes and withdraws an ACSL count instruction. These are documented context changes, not evidence that a verdict is wrong. Their effects cannot be separated from grader effects here.
- Line counts are deliberately outside the paired conclusion: original decks use inclusive physical spans (comments/blanks retained) and varied closure partitions; the new M9 deck uses nonblank/non-comment code and common proposition-suite closures. C bodies/tables also change partition. No replication of M5 or exact M9 line counts is claimed.
- Generator/harness facts in `bench/results.md:115,119` are reported rather than re-audited: fixed generator model/CLI, but T2 spans the reaper interruption and parallel → serial scheduling. The regrade holds outputs fixed, so it cannot establish that underlying arm differences were caused only by FVA or remove any scheduling/provider drift. It also supplies no new cost evidence.

### K1 — established methodological context, bounded transfer

Zheng et al., *Judging LLM-as-a-Judge with MT-Bench and Chatbot Arena*, arXiv:2306.05685, https://arxiv.org/abs/2306.05685. Verbatim abstract excerpt: “We examine the usage and limitations of LLM-as-a-judge, including position, verbosity, and self-enhancement biases, as well as limited reasoning ability, and propose solutions to mitigate some of them.” Source fetched with `webtext https://arxiv.org/abs/2306.05685`, rc 0.

That work evaluates chat-response preference judgments, not Lean/ACSL faithfulness or this systems-programmer persona. It supports treating these mechanisms as plausible threats requiring controls; it supplies **no transferable error rate** and no evidence that a particular bias occurred in D54. Here the non-identification is also direct: old arm contrasts and old judge identities coincide; new grader identity, packet order, workload/context, masking and some prompt detail change together. There is no randomized counterfactual in which only masking changes.

## Probe P1 — exact paired recomputation + scope sensitivity

Command below reads only the supplied artifacts; standalone Python stdlib via `uv`, isolated imports. Output recorded below. It checks exact table/key coverage, recomputes raw differences without using `comparison.md`, checks the saved M9 join, and plants one in-memory M3 discrepancy as a positive control.

```bash
uv run --no-project python -I - <<'PY'
from pathlib import Path
from collections import Counter
R = Path(".")
D = R / '.scratch/mq/d54'
key = dict(x.split('\t') for x in (D/'private/key.tsv').read_text().splitlines())
assert len(key) == len(set(key.values())) == 20
old, new = {}, {}
def rows(p):
    for line in p.read_text().splitlines():
        if line.startswith(('| J', '| K')):
            c = [x.strip() for x in line.split('|')[1:-1]]
            if c[0][1:].isdigit(): yield c
for n in range(37, 45):
    for c in rows(R/f'.scratch/teammates/reviewer-{n}/verdicts.md'):
        m, q = c[2].split(maxsplit=1)
        k = (c[1], m, '-' if m == 'M6' else q)
        assert k not in old
        old[k] = c[3]
for part in ('m3', 'm9'):
    for c in rows(D/f'reviewer-d54-{part}/verdicts.md'):
        m, q, v = c[2:5] if part == 'm3' else ('M9', c[2], c[3])
        k = (key[c[1]], m, q)
        assert k not in new
        new[k] = v
expected = {(r,m,q) for r in key.values()
            for m,qs in [('M3',('R1','R2','R3')),('M6',('-',)),('M9',('R1','R2','R3'))]
            for q in qs}
assert set(old) == set(new) == expected
print('SCHEMA', len(key), len(old))
for m in ('M3','M6','M9'):
    ks = [k for k in old if k[1] == m]
    print(m, 'agreement', sum(old[k] == new[k] for k in ks), '/', len(ks),
          'old', dict(Counter(old[k] for k in ks)), 'new', dict(Counter(new[k] for k in ks)))
for arm in ('bare','prompted','fva','tool'):
    runs = sorted(r for r in key.values() if r.startswith(arm+'-'))
    for scope in ('all','R2R3','three-weaker'):
        rs = runs if scope != 'three-weaker' else [r for r in runs
              if all(old[(r,'M3',q)] == new[(r,'M3',q)] == 'weaker' for q in ('R1','R2','R3'))]
        qs = ('R2','R3') if scope == 'R2R3' else ('R1','R2','R3')
        ks = [(r,'M9',q) for r in rs for q in qs]
        print(arm, scope, len(rs), len(ks), sum(old[k]=='readable' for k in ks),
              sum(new[k]=='readable' for k in ks), 'changed-runs',
              len({k[0] for k in ks if old[k] != new[k]}))
for r in sorted(r for r in key.values() if r.startswith('fva-')):
    print(r, [(q,old[(r,'M9',q)],new[(r,'M9',q)]) for q in ('R1','R2','R3')])
joined = {}
for line in (D/'m9-join.tsv').read_text().splitlines():
    k,a,b = line.split('\t'); r,q = k.split(':'); joined[(r,'M9',q)] = (a,b)
assert joined == {k:(old[k],new[k]) for k in old if k[1]=='M9'}
planted = dict(new); planted[next(k for k in new if k[1]=='M3')] = 'false claim'
assert sum(old[k] != planted[k] for k in old if k[1]=='M3') == 1
print('JOIN + POSITIVE CONTROL PASS')
print('illustrative 0/5 iid bound', f'{1-.05**(1/5):.6f}')
PY
rc=$?; printf 'probe_rc=%s\n' "$rc"; exit "$rc"
```

Observed output (arm/scope columns = retained runs, requirement rows, original readable, new readable):

```text
SCHEMA 20 140
M3 agreement 60 / 60 old {'not proven, reported': 4, 'weaker': 56} new {'not proven, reported': 4, 'weaker': 56}
M6 agreement 20 / 20 old {'none': 20} new {'none': 20}
M9 agreement 53 / 60 old {'readable with effort': 40, 'readable': 20} new {'readable': 27, 'readable with effort': 33}
bare all 5 15 0 0 changed-runs 0
bare R2R3 5 10 0 0 changed-runs 0
bare three-weaker 5 15 0 0 changed-runs 0
prompted all 5 15 0 0 changed-runs 0
prompted R2R3 5 10 0 0 changed-runs 0
prompted three-weaker 5 15 0 0 changed-runs 0
fva all 5 15 5 12 changed-runs 3
fva R2R3 5 10 2 8 changed-runs 3
fva three-weaker 1 3 0 0 changed-runs 0
tool all 5 15 15 15 changed-runs 0
tool R2R3 5 10 10 10 changed-runs 0
tool three-weaker 5 15 15 15 changed-runs 0
fva-lz4-c-1 [('R1', 'readable with effort', 'readable'), ('R2', 'readable with effort', 'readable'), ('R3', 'readable with effort', 'readable')]
fva-lz4-c-2 [('R1', 'readable', 'readable'), ('R2', 'readable', 'readable'), ('R3', 'readable', 'readable')]
fva-lz4-c-3 [('R1', 'readable', 'readable'), ('R2', 'readable with effort', 'readable'), ('R3', 'readable with effort', 'readable')]
fva-lz4-c-4 [('R1', 'readable', 'readable'), ('R2', 'readable with effort', 'readable'), ('R3', 'readable with effort', 'readable')]
fva-lz4-c-5 [('R1', 'readable with effort', 'readable with effort'), ('R2', 'readable with effort', 'readable with effort'), ('R3', 'readable with effort', 'readable with effort')]
JOIN + POSITIVE CONTROL PASS
illustrative 0/5 iid bound 0.450720
probe_rc=0
```

Replay directly from this report's first bash block also returned `report_replay_rc=0`. No target artifact or grade changed.

## Coverage + checks

- Completion validator = PASS, rc 0: five ordered verdict rows, allowed verdict vocabulary, five keyed detail sections, one final marker; seed-token positive control = count 1/rc 0, completed file = count 0/grep rc 1 (expected no-match status); 11/11 decisive source anchors match. First anchor pass returned rc 1 (`IndexError`) on an out-of-range README citation; corrected R1's line 19 → 16 and reran successfully. Numerical probe and its report-embedded replay both passed, rc 0.
- Read whole: comparison; two D54 decks/briefs; directive file; key/join; all eight original decks/briefs; original common T2 templates; rubric including addenda; corrected T2 README; five fva packet specs + P07 access definitions. Read relevant result summary, grading-history, T2/T3, T4/T5 sections; other-task individual submissions not inspected.
- Targeted statement reading = fva packets only, selected to inspect the R1 contrast and disputed M9 burden; **not** a third independent regrade of all 20 submissions. No full packet/archive equivalence audit, model-provenance audit, production log audit, theorem builds, replay, runtime, timings, M5 recount or human test run.
- Brief keyword probe executed read-only: own-observable/final-store rule absent from reviewer-37's initial brief, present in 39/41/43 + D54; explicit-partial/split-table wording absent in 38/40, present in 42/44 + D54; `brief_probe_rc=0`. Anchored source excerpts above settle the wording question; absence is not inferred from a failed command.
- BrowserOS Neo connection reported 503; no shared browser/account state changed. Public methodological abstract read by the configured `webtext` source reader, rc 0; no authenticated/paywalled content needed.
- Still unconfirmed: exact grader model/version/effort pins and backend stability; masking success; complete mid-run prompt history; independent detector sensitivity; human comprehension; transport to other tasks. Each missing check is named above rather than treated as passed.

## Implications + next tests, ranked by information value

1. **Crossed replication on existing artifacts, before more generation runs.** Freeze full prompt/rulings/reference bundle and evaluator pins; add another model family and within-family repeats, every judge across every arm, counterbalanced packet order with hidden duplicates. Lock raw scores before MAIN adjudication. Discriminates judge-family/threshold/order variance; reports per-run and per-arm confusion tables, not just pooled agreement. Positive/negative over-claim and observable-scope controls supply the missing validity check.
2. **Transport to new judgment boundaries.** All-arm T4 + T5 first (bio persona, refutations, tolerance/tie-policy faithfulness), then remaining tasks before a benchmark-wide claim. Prespecify cases/tasks and report every result; selecting only favorable task/metric comparisons creates a further selection problem. No row-level significance claims or unplanned multiple-testing leaderboard.
3. **Paired presentation test on borderline M9 rows.** Preserve denotation and proof scope; counterbalance decimal/hex bytes, positional/named cases and explicit state setup across both FVA and non-FVA statements. If labels follow presentation while meaning stays fixed, readability formatting is a testable mechanism; if only one family shifts, proxy calibration is the issue. Hypothesis, not finding: removing an authored interpreter puts shared-base statements nearer a subjective effort threshold, explaining why all disagreements cluster in fva while custom-interpreter rows stay stable.
4. **Generation-mechanism test only if a causal library claim is needed.** Compare frozen FVA with/without reviewed access-footprint vocabulary under the same generator/harness conditions; score access-level coverage, full-run faithfulness, review surface and cost jointly. This separates “library vocabulary guides proofs” from a fortuitous sample and avoids rewarding a smaller but weaker statement. Not necessary to report this D54 sensitivity result.

Recommended shipped interpretation: **“A common label-masked grader reproduced T2's M3/M6 verdicts. M9's Lean-arm ordering remained, but seven FVA readability ratings changed before adjudication. This checks T2 under the stated rubric; other tasks and human readability remain untested by the regrade.”**

scientist-d54-DONE-1
