# U20 method ruling — MAIN draft (for ≥ 5 consultants, then the advisor, then the user)

Status: M2, M3 + round 2 landed (`measure/{m2,m3,r2,r2-m2}.tsv`, summary `measure/summarize.py`). Harness `measure/measure.sh`, contract form: M2 = 1 warm-up + 3 fresh
`lake env lean` runs per arm module, CPU 7 pinned, arm order rotated per run; M3 = CPU-pinned
`leanexport` of the cumulative roots + leanchecker/con-leche, 3 rounds interleaved across arms.
Host = i7-8650U laptop (4C/8T; CPU 7's SMT sibling = CPU 3), shared with the user's other sessions
(load average up to 8.2): M2 runs 2–3 of D+ and run 2 of V ran slower (D+ 252–254 s vs 206 s;
V 1143 s vs 649 s), C's runs did not (the load as cause = inference from the load average) ⇒ Σ minima
(each module's minimum observed time) reported beside Σ medians; neither is an uncontended-speed
estimate.

## Question
Which engine proves the decoder's remaining cutpoints (SegB, SegD; ExtL1B done engine-neutrally;
SegC exists in both finalists) and later compiled-code subjects: C (verified block evaluator `blockEval` + `wasm_eval`)
or D+ (automated small-step `wasm_dstep` over `Ref.seq` + `DirectContext`)? V (vcgen over a WP
instance) = third arm.

## Fixed facts (not reopened)
- Frozen rule 3 → round 1 inconclusive (contract § Round 1 outcome; scientist-2 C1: robust to ±1
  line/stage, conditional on C and D+ staying eligible after replay).
- I7 fit neutralized: `Sim.lean` consumes the frozen cutpoint statements for any engine
  (scientist-2 C5: neutralizes interface compatibility, not the cost of reaching the interface).
- Proven by MAIN with the checkpoint-1 machinery (`wasm_cstepu`/`wasm_within`): Entry, ErrRet,
  SegA (`Cut/ExtB`, 448f18e: ExtL1B = checkpoint 1's route-D loop proof with the bound exit kept);
  composition R1–R3 ⇐ cutpoints (`Top.lean`, `Sim.lean`). Open for the engine: SegB, SegD (+ the
  winner's S1–S5 + SegC merged).
- Engines are untrusted tooling: kernel-checked, zero review surface, zero trusted base.

## Evidence table (per arm)
| coordinate | C | D+ | V |
|---|---|---|---|
| (a) new + changed lines S1/S2/S3/S4/S5 (rule 2a; C's S2 and D+'s S5 each change 1 earlier line) | 511/633/113/26/368 = 1651 | 505/638/164/34/342 = 1683 | 553/778/335/119/663 = 2448 |
| (b) M0 min S1/S2/S3/S4/S5 | 33.8/43.3/5.0/1.0/34.1 = 117.2 | 46.8/36.2/8.9/1.4/59.5 = 152.8 | 69.3/37.0/23.9/4.5/105.6 = 240.3 |
| (c) fresh build of arm modules (M2, runs 1–3 after a warm-up: Σ module medians / Σ minima; per-run Σ range; slowest module median) | 120.5 / 118.2 s; 120–128 s; S1 17.6 s (S5 17.2 s) | 226.0 / 205.5 s; 207–254 s; S5 64.4 s | 622.4 / 526.6 s; 528–1143 s; ShortCopies 88.2 s |
| (d) export bytes of cumulative S1…Sk − baseline (45,047,166 B), MB, k = 1…5 | 81.2 / 92.2 / 94.0 / 94.1 / 100.9 | 80.3 / 90.8 / 92.6 / 92.6 / 100.7 | 85.6 / 107.1 / 108.3 / 108.6 / 115.6 |
| (e) replay of the S1–S5 export, leanchecker / con-leche, median (min–max) of 3 interleaved rounds; baseline 6.8 / 9.2 s | 52.4 (50.5–56.0) / 60.4 (59.3–62.6) s | 53.7 (53.0–60.1) / 63.0 (62.6–63.2) s | 52.8 (52.4–62.8) / 61.7 (61.2–62.9) s |
| (e′) `--paranoid`-only kernels on the same S1–S5 export (`measure/paranoid.tsv`, one run each, unpinned, host shared with two proof builds): leanchecker-paranoid / lean4lean / nanoda / con-ron | accept 72.2 s / decline 26.6 s (deep recursion at `instrStep_sound`, FVA's documented lean4lean limit; the replay rule allows declines) / accept 10.5 s / accept 12.6 s | accept 76.1 / decline 26.6 / accept 10.0 / accept 13.1 s | not run |
| eligibility (rule 1: 5/5 frozen roots, standard axioms, both default checkers accept; rule 4: replay ≤ 10 min, every module ≤ 10 min) | eligible (max replay 62.6 s; max module run 19.0 s, 37.4 s incl. warm-up) | eligible (63.2 s; 79.3 s) | eligible (62.9 s; 174.5 s) |
| gate hygiene (`lake --wfail` of the arm modules) | clean | clean | rc 1: 40 linter warnings |
| round 2 SegC: (a) lines (infra/specific) | 247 (9/238) | 287 (30/257; 7 = `xor32_not`, 23 scaffolding) | not run (round 2 = eligible finalists) |
| round 2 SegC: (b) M0, contended | 22.8 min, 8 builds, 43 tools | 32.2 min, 7 builds, 46 tools | — |
| round 2 SegC: D3 exec glue / induction+model / plumbing | 73 / 58 / 116 | 67 / 42 / 178 | — |
| round 2 SegC: MAIN acceptance (`example : SegC := …` + axioms); module build (r2-m2: Σ medians / Σ minima); export of the segC root; replay lc / cl median (min–max), contended (load average up to 18: the user's concurrent Verus/z3 job) | rc 0, standard axioms; 23.2 / 19.7 s (1 module); 128.7 MB; 85.0 (80.2–99.8) / 96.5 (90.1–99.5) s | rc 0, standard axioms; 56.1 / 55.7 s (3 modules; SegCLoop 42.1 s); 126.9 MB; 105.2 (51.2–117.0) / 94.7 (50.7–96.6) s | — |
| rounds 1 + 2 lines (new + changed) | 1898 | 1970 | — |
| engine library lines | 265 (`Block*.lean`) | 232 (`Direct*.lean`) | 113 (`Wasm*WP.lean`) |

Per-stage winners on lines: C = S3 (−51), S4 (−8), SegC (−40), totals; D+ = S5 (−26); S1/S2 within
±6. On M0: C = S1, S3, S4, S5, SegC; D+ = S2. n = 1 author per arm (author × engine confounded).

Rule 3 with (c)/(e) (contract § Selection rule): C and D+ each dominate V (≤ on (a) total + S5;
within 2× on (b), (c), (e)); C vs D+ cross on (a) (C total 1651 < 1683, D+ S5 342 < 368) ⇒ no lone
dominant arm ⇒ inconclusive ⇒ qualitative ruling between C and D+; V out as dominated (+ 40 linter
warnings under `--wfail`). All three arms eligible (rule 1 + 4).

## Qualitative criteria (contract § Selection policy, minus I7 fit)

### Cost on the remaining decoder
- Remaining for the engine: SegB (general literal path: room checks, `memmove` via S2 near the end,
  the S3 wildcopy, the offset read), SegD (offset check, prologue: 8-byte `memcpy` or the offset < 8
  tables + byte copies, matchRest: S4 far from the end, near it a third wildcopy to `oend − 7` + the
  byte loop I3).
- ExtL1B (done, 448f18e) ≠ a SegC transfer (scientist-3 phase A, `Cut/SegA.lean:145–154`): it keeps
  checkpoint 1's generic premises (any `acc < 2^31`, `lim ≤ mem.size`, no 2 MiB cap) and its
  reachable overflow exit; both SegC proofs used the 2 MiB profile to rule the overflow guards out.
  Proven engine-neutrally by checkpoint 1's route-D proof with the bound exit kept (`Cut/ExtB`).
- SegB/SegD = S5-shaped work (branches, joins, callee contracts, nested labels) plus one new
  byte-loop class (I3, memory-evolving). S5 = the closest evidence: D+ 342 vs C 368 lines; M0 C
  34.1 vs D+ 59.5 min.
- SegC's C advantage = plumbing (+62 for D+), not execution (D+ −6) or model (D+ −16)
  (scientist-3 phase A; D3 tables). The plumbing gap tracks state representation (C: explicit
  19-slot local lists the evaluator computes through, `cLocals`; D+: abstract `ls` + `getElem?_set`
  chains + `CMInv` updates); either engine can adopt the other's representation ⇒ weak engine
  evidence (scientist-2 C2).

### Agent fit (researcher-4)
- Successful large compiled-code developments = human-designed abstractions + reusable contracts +
  mechanical execution + agent-sized math goals (R4.1–R4.6); no controlled comparison of interfaces.
- Both engines expose that shape. C: per block = code slice + fuel + facts → one `wasm_eval` →
  final configuration + `TraceOK` footprint goal; per loop = invariant + induction; per call =
  contract + `Until.trans`. D+: per block = `iterate N wasm_dstep [facts]`, one step per instruction;
  same loop/call pattern.
- Friction seen: C — explicit byte-range facts for write-conditioned loads (S1), concrete
  big-literal states → kernel deep recursion (S2, fixed by symbolic BitVec bases), maxRecDepth 4000
  for nested-label simplification (SegC). D+ — simp memory bookkeeping (pre-proved
  `instrStep_load8/store8`), wrapped-i32 bias payload growth → kernel deep recursion at 277 s /
  20.8 GB and 22.8 GB RSS (S2 builds 47, 50; fixed by abstraction), two stopped S5 local-sorting
  attempts (278 s, 453 s), S5 module 64.4 s in M2 (C's: 17.2 s). V — monolithic WP exhausted
  4M heartbeats; multi-call inference produced false obligations; fixed by join-point contracts.

### Maintainability
- Both iterate the reference stepper (`seq`/`seqUnique`), so neither duplicates the instruction
  interpreter; a new instruction may still need normalization, uniqueness or footprint lemmas (or an
  engine adjustment) in either (scientist-3 E5d). C = one evaluator definition
  + one generic soundness theorem (`blockEval_until`, by induction on fuel) + tactic; D+ = one step
  tactic + `DirectContext` transport.
- Kernel cost: similar. Exports of the S1–S5 closures differ by 0.3% (C 100.9 MB, D+ 100.7 MB above
  the baseline) and replay medians by ≤ 5% (leanchecker 52.4 vs 53.7 s, con-leche 60.4 vs 63.0 s);
  con-leche favors C slightly; neither a practical advantage nor equivalence is established
  (scientist-3 E4/E5d). Most export growth comes with S1 (+80 MB; how much is shared stepper/library closure is not
  isolated); S2–S5 add 20 MB together.
- Elaboration cost (fresh process, prebuilt imports): C's arm modules take about half D+'s time
  (summary ratios 0.53 / 0.58 = Σ medians 120.5 vs 226.0 s, D+'s raised by contention, and Σ minima
  118.2 vs 205.5 s; not a confidence interval), its
  decoder-shaped S5 0.27× (medians 17.2 vs 64.4 s), 0.34× when every module the S5 checkpoint
  added or changed is charged (C 5 modules 28.3 s, D+ 7 incl. the changed `Direct` 83.4 s, V 12
  modules 230.4 s; scientist-3 phase B); C's advantage holds in every observed run total (C 120–128
  s, D+ 207–254 s). This workload = fresh recompilation of affected proof modules (e.g. the gate's
  subject builds after an upstream change); not a measured full-gate or incremental-edit speedup.
  Replay costs are similar.

## Draft ruling
**C — the verified block evaluator — for SegB and SegD, provisionally, and as the default to test
on later compiled-code subjects: C has the lower observed fresh-elaboration cost among the completed
implementations on this decoder; bounded readiness, not method superiority (scientist-3 E5d: a
defensible policy choice, not a compelled empirical winner — rule 3 stays inconclusive).** Checkpoint 1's stepping
(`wasm_cstepu`/`wasm_within`) stays as the fallback for any block the evaluator handles badly; both
produce `Until`/`Within` and compose by `Until.trans` (as Entry, ErrRet and ExtB already do). D+'s
tactic library is not merged (one engine to maintain); V is out (dominated).

Grounds, in order of weight:
1. Elaboration cost (measured; fresh-process, prebuilt-import workload): C about half D+ on the
   arm's modules, about a third on everything the S5 checkpoint added or changed; the direction holds
   in every observed run total; replay + export similar. Recurs with every fresh recompilation of
   affected proof modules.
2. Authoring cost (measured, author-confounded, no engine effect identified — scientist-3 E3): C
   lower on totals (1651 vs 1683; with SegC 1898 vs 1970) and on M0 in 5 of 6 stages (117 vs 153
   min round 1; SegC 23 vs 32 min); D+ lower on S5 lines (342 vs 368).
3. Engine boundary (design, not measured): one evaluator over the reference stepper + one generic
   soundness theorem (`blockEval_until`) = the D9 option the user named ("automated block
   summaries"); its next steps (fuel up to the next branch/call/join, uniform byte-range discharge)
   are a design hypothesis, not a measured cost. D+'s next steps (focus/unfocus adapters,
   local-update identities) are proof-plumbing automation either engine could add.
4. Failure modes: both hit normal-form/recursion trouble (scientist-3 E5c); D+'s S2 attempts
   reached 20–23 GB RSS (builds 47, 50), and two S5 attempts were stopped at 278 s and 453 s
   (≈ 2.9 GB RSS); C's worst = kernel deep recursion on concrete big literals (S2, fixed by symbolic
   bases) and `maxRecDepth 4000` (SegC). This history does not establish a lower worst-case bound
   for C.

What it does not claim: superiority, future-subject scaling, agent usability for other authors
(n = 1 author per arm; SegC isolates engines weakly — scientist-2 C2, scientist-3 E3). The user's
maintenance preference may still favor D+ without contradicting rule 3 (D+ keeps the smaller S5
and the continuity with checkpoint-1 stepping).

Reversal evidence (scientist-3 E6b): on a SegB/SegD block, C repeatedly hits a resource obstruction
(kernel deep recursion, a build over the 12 GiB cap) or an independent-checker rejection or
replay-resource failure that same-strength stepping avoids on the same block, domain and limits;
also a coverage stall or unacceptable proof size or iteration cost. One such block → stepping there
(both compose by `Until`); a second → reopen the default with the evidence (a policy threshold);
a failure in the shared evaluator or at the full roots, or one that blocks a milestone, reopens the
default at once (consultants 4, 5); an unfinishable milestone is reported at once (the user's stop
rule). S5's figures (368 lines,
34 min, 17 s build) are a descriptive reference, not a gate. The full roots' export + replay are
measured when assembled (actual union growth, no per-instruction projection).

## Unit plan sketch (pre-mortem input)
- `.scratch/u19c2/unit-plan-draft.md` (U21 merge C … U28 report + close).
- Merge C (engine + S1–S5 + SegC) squash; archive tags `archive/spike-{c,d,v}`; worktrees +
  branches removed.
- SegB (MAIN) ∥ SegD (spike-c revived, its worktree); Proof.lean r1–r3 from `Top` + cutpoints;
  test-subjects subject entry + surface pin (88, or 76 if the factored spec is adopted); fva trust
  default + `--paranoid`; milestones 1 + 2.

## Consultant verdicts (5 independent; consultant-{1..5}.md) + MAIN's handling
| row | verdicts | conditions raised | handled |
|---|---|---|---|
| Q1 engine | agree ×2, agree with conditions ×3 | C = provisional artifact-level default, not a rule-3 winner; later subjects need new readiness checks; keep the stepping fallback | ruling text says so (draft ruling § first paragraph) |
| Q2 V out | agree ×4, with conditions ×1 | eligible but dominated; 40 warnings = a separate shipping defect; refresh the contract's stale Status | contract Status refreshed in the ruling commit |
| Q3 confounds | agree with conditions ×5 | "minimum observed", contention as inference, new + changed accounting (1651 / 1683; D+ S5 342), S1 export attribution unisolated | applied |
| Q4 risks | agree with conditions ×5 | SegD = the largest gap (offset < 8 tables, wrapped pointers, error after writes, near-end tail; I3 tail ≤ 2 bytes); exact state + footprint acceptance | SegD = frozen exact statement; both teammates audited it vs the WAT (no issue) |
| Q5 operability | open ×5 | full roots + the 4 `--paranoid`-only kernels + all-subject load unmeasured | paranoid kernels run on the S1–S5 exports (row e′: accept / documented decline); the full union = U21 replay checkpoint; final trust runs measured |
| Q6 reversal | agree with conditions ×5 | same block, domain, limits; a shared-engine or milestone-blocking failure reopens at once; 2 blocks = policy | applied |
| Q7 change | agree with conditions ×5 | U21 = replay checkpoint with all 6 kernels (×3); milestone 1 = interim R1-only claim module + a proof typed by it (×2) | unit plan U21, U25, U26 |
