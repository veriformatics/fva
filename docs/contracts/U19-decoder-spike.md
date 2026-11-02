# U19 contract — decoder feasibility spike: lz4 C `LZ4_decompress_safe` on its bytes (tiers: footprint vocabulary = kernel, reviewed once; access checker = verified impl; subject proofs = shallow, kernel-checked by `fva trust`; route measurements = data a `Decisions` entry rests on → `scientist`)

Purpose (Decisions: Next unit): decide whether FVA's stack proves all-input claims about a real-size compiled decoder, and which proof route scales. Bench v2 left this unshown: largest all-input proof ≈ 139 instructions (D9), no arm proved a T2 requirement over its whole domain, R1 needs an access footprint FVA could not state (D52). Prior art (bounded survey, `.agent/archive/u19/researcher-{1,2,3}.md`): no completed LZ4 decoder proof and no controlled direct-vs-refinement comparison in the sources inspected (Theorem Labs' LZ4 statements open); Certora's zlib `inflate_table` memory safety = 266 C lines, 7 loops, ≈ 20,000 Lean lines (source level).

Subject: `bench/subjects/wasm/lz4-c.wasm` (8,469 B, sha256 `8b73efb6…`; lz4 v1.10.0 `lib/lz4.c`, BSD-2-Clause), copied to `FVATest/Subjects/Lz4C/` with a NOTICE. Func 2 = `LZ4_decompress_safe`: 550 instructions, 7 loops, 53 branch opcodes, 11 calls (safe decode loop only: `LZ4_FAST_DEC_LOOP` = 0 off x86/aarch64); callees func 3 = `memcpy` (93 instructions, 10 call sites), func 4 = `memmove` (191, 1 call site), byte loops from `bench/subjects/c-memory.c`.

Status rule: checkpoint 1 proves a frozen loop lemma; only checkpoint 2's complete R1–R3 theorem earns the spike's pass. A close without checkpoint 2 = partial/inconclusive evidence + the precise blocker, then the user rules the next scope (IMPLEMENT = a fresh session). Route status per route: proved / failed obligation / infrastructure blocked / not attempted, with commands + measured effort.

## Seam (MAIN, before either route; route-independent)

- A1 Footprint vocabulary (D52), reviewed spec `FVA/Spec/Exec/Access.lean`: `Reads c ma a` / `Writes c ma a` = the next step of `c` is a successful guest `load`/`loadPacked` (`store`/`storePacked`) of the memory at store address `ma` covering byte `a`; base cases = those rules' redexes + premises verbatim, context cases = `Step`'s `seq`/`label`/`frame`. Scope = successful guest byte accesses: bulk instructions access through the packed steps they expand into; trapping accesses, `memory.grow` and host-call store effects are no accesses (footprint claims concern import-free modules).
- A2 Claim forms: `Within R W c` = every `(ma, a)` the next step reads satisfies `R ma a`, every one written `W ma a`; `Throughout H P c` = `P` at every `Steps`-reachable configuration (A1 module). `CallWithin H s inst name args R W` (`FVA/Spec/CAbi.lean`) = the export resolves to `fn`, `InvokeOK s fn args`, `Throughout H (Within R W) (invokeConfig s fn args)`. Safety only: total correctness stays with `CallReturns` on the same prepared invocation.
- A3 Verified checker `FVA/Impl/Exec/Access.lean` (`access c`, by the stepper's traversal) + `FVA/Proof/Exec/Access.lean` (`reads_iff`, `writes_iff`). Proof library `FVA/Proof/Lib/Footprint.lean`: `MustW H R W Q c := Must H Q c ∧ Throughout H (Within R W) c`; `Until H P Q` (`done : Q c`; `next : P c`, a successor exists, every successor satisfies `Until`) = total arrival at `Q` with `P` on every configuration strictly before arrival; transport only with a tail: `mustW_of_seq` (current `Within` + unique successful step + `MustW` at the successor), `mustW_of_until` (`Until H (Within R W) Q c` + `MustW` from every `Q` configuration), final configurations close `MustW` (no successor); choice points rejected (`uniqueStep`). Tactic `wasm_step1w` = `wasm_step1` on a `MustW`/`Until` goal + the step's `Within` obligation (`access = none` by simp, else the range goal).
- A4 Negatives, each seen red first: (a) a nested-frame test program (caller → callee frame → `i32.store8` at a constant address) proves `¬ CallWithin` for a `W` excluding that byte (a reachable `Writes` outside) and `CallWithin` for one including it; (b) the same with `i32.load8_u` and `R`; (c) `instrAccess` endpoint mutated (`ea + n` → `ea + n + 1` bound, or `start` off by one) → `reads_iff` fails to build, recorded; (d) `Reads.frame` deleted from the spec → (b)'s rejection theorem (`¬ CallWithin`, which exhibits a `Reads` inside the callee frame) fails to build, recorded — deleting a case weakens the relation, so only a rejection fires. Mutation check: `Impl/Exec/Access` joins the `exec` group; its mutants must break a theorem or test.
- A5 Subject package `FVATest/Subjects/Lz4C/`: `Lifted.lean` + NOTICE; `Instance.lean` = every fresh instance is `(store0, alloc.2)` (`instance_eq`, data segment by kernel-evaluated `runDet` + `Must.outcome`); func-2 slices + label contexts kernel-checked against `Lifted.func2`.

## Checkpoint 1 — one loop, two routes, one frozen statement

- Loop = the literal-length extension (`read_variable_length` inlined, func 2 `loop @10`, WAT 3593–3614): per iteration `p' = p + 1`, error exit `br 7 (@3)` when `p' > lim` (local 14 = `iend − 15`), `acc += mem[p]`, error exit when `acc` is negative as i32 (overflow guard), continue while `mem[p] = 255`, normal exit by fall-through to the code after block `@9`. Chosen over the byte match copy, which runs ≤ 2 iterations on real paths (scientist-1 S5, consultant-1 K6): it carries parsing, a bound guard, an overflow guard and two exits.
- Statement L1 (frozen before either route; proof-side, declarative — no recursive model function): entry = func 2 at `loop @10` with locals `2 = p`, `17 = acc`, `14 = lim` (unsigned, `p ≤ lim` — the pre-loop guard admits `p = lim`, whose first iteration takes the bound exit with `k = 0` —, `lim + 1 < 2^32` so `local4 = p + 1` never wraps, `lim ≤ mem.size` so every read is in bounds, `acc < 2^31`), every other local arbitrary, memory 0 holding bytes `b j = mem[p + j]`, under the exact label contexts `@9 … @3` (slices of `Lifted.func2`) and an arbitrary outer context. Conclusion = `Until H (Within R W) Exit entry` with `R ma a := ma = 0 ∧ p ≤ a ∧ a < lim`, `W := ⊥`, where `Exit` holds exactly at: (normal) the configuration running the code after block `@9`, with some `k` such that `b j = 255` for `j < k`, `b k ≠ 255`, `p + k + 1 ≤ lim`, every partial sum `acc + Σ_{j ≤ i} b j < 2^31` (`i ≤ k`), locals `2 = 4 = p + k + 1`, `15 = b k`, `17 = acc + Σ_{j ≤ k} b j`; (bound error) the configuration after `br 7` reaches block `@3`'s continuation, with `k` such that `b j = 255` and partial sums `< 2^31` for `j < k`, `p + k + 1 > lim`, locals `2 = p + k`, `4 = p + k + 1`, `15 = b (k − 1)` and `17 = acc + Σ_{j < k} b j` when `k > 0` (entry values when `k = 0`); (overflow error) the same continuation with `k`: `b j = 255` for `j < k`, `p + k + 1 ≤ lim`, partial sums `< 2^31` below `k`, `acc + Σ_{j ≤ k} b j ≥ 2^31`, locals `2 = p + k` (`local.set 2` follows the overflow test), `4 = p + k + 1`, `15 = b k`, `17` = that sum mod 2^32. Every exit: every other local equals its entry value, the store is unchanged.
- Route D (direct): invariant over `Config` + induction on `lim − p`, `wasm_step1w` per instruction.
- Route R (refinement): proof-side model `extModel` (state = locals + read log, one step per iteration, recursion on `lim − p`) + a simulation lemma (one wasm iteration ↔ one model step, read addresses included; finite stuttering allowed) + a model-level proof of L1's `Exit`; the model is never imported by a spec module.
- Comparison check (scientist-1 protocol, frozen here): a paired engineering case study, not a causal route comparison. Common seam = separately recorded setup cost; both routes prove the same L1 with the same axioms + checker set.
  - M0 active effort (MAIN wall time on the route, failed attempts, validation waits); M1 `codeLines` split stepping/simulation vs model/spec reasoning vs generated; M2 route-module elaboration wall + max RSS: one warm-up, then 3 interleaved paired fresh-process runs on a fixed CPU set (`taskset`), all observations kept; M3 export bytes/time + per-checker replay time/RSS/status on the route's closure (default checkers); M4 = one fixed `-O2 → -O1` rebuild (same sources, clang, other flags): whole-artifact + region structural delta recorded before repair, then L1 re-established on the corresponding region, added + deleted hand-written lines apart, active repair effort, full elapsed cost; repair order reversed from build order; a split/removed region = an outcome, never a substitute loop; M5 descriptive lines/seconds per static node and per proved step, no extrapolation.
  - Selection: complete equal-strength proofs within budget are eligible; a Pareto-dominant route on (M0, M4 effort, M2, M3) wins; a runtime "≥ 2×" label needs `min(slower) ≥ 2 × max(faster)` over the paired runs, else that coordinate is inconclusive; a trade-off = inconclusive → route D provisionally for this spike (existing machinery), recorded as policy, not a scaling result.
  - Budget: each route ≤ 6 h wall-clock of MAIN's active work on it (start/stop timestamps logged in `.agent/archive/u19/routes.md`, waits for builds included) or 400 tool calls, whichever comes first; exhaustion = "not completed under these conditions" + last failed obligation + command/rc.
- Failure taxonomy (recorded per attempt): ill-posed statement | missing reusable lemma | unresolved subject invariant | elaboration limit | exporter/checker limit | budget exhausted.

## Checkpoint 2 — the full theorem (only after checkpoint 1 holds)

- Gate to attempt it here: an obligation inventory of func 2 + callees (entry/zero-capacity paths, each loop family, branch exits, `memcpy`/`memmove` summaries with footprints + sequential-copy semantics on overlap, alias/frame facts, the LZ4 format relation, termination, malformed-input exits), each class tagged established / new lemma / untested; checkpoint 2 starts in this session only when every class has a demonstrated pattern and the inventory's conservative effort allowance fits the session; otherwise U19 closes partial (Status rule) with the inventory as IMPLEMENT's starting plan.
- Claims `FVATest/Subjects/Lz4C/Spec.lean` (task `bench/tasks/lz4-c/README.md` R1–R3), for every `src dst : Nat`, `input initDst : List UInt8` with `131072 ≤ src`, `src + input.length ≤ 2097152`, `131072 ≤ dst`, `dst + initDst.length ≤ 2097152`, `input.length < 2^31`, `initDst.length < 2^31`, disjoint unless one buffer is empty (`input = [] ∨ initDst = [] ∨ src + input.length ≤ dst ∨ dst + initDst.length ≤ src`; user ruling, `.agent/spec.md` Decisions; stated once as `Buffers` in `Call.lean`, with the prepared call as `OnCall`); `ps = [.write src input, .write dst initDst]`; args = `BitVec.ofNat 32` of `src dst input.length initDst.length`; `∀ H, ∃ s inst, Prepared Lifted.module H ps s inst` and, for every prepared instance:
  - R1 = `CallWithin` with `R ma a := a < 131072 ∨ 2097152 ≤ a ∨ (src ≤ a ∧ a < src + input.length) ∨ (dst ≤ a ∧ a < dst + initDst.length)`, `W ma a := a < 131072 ∨ 2097152 ≤ a ∨ (dst ≤ a ∧ a < dst + initDst.length)`, and `CallReturns` with one `i32` result;
  - R2 = `Lz4.Valid input c ∧ c.length ≤ initDst.length ∧ (1 ≤ initDst.length ∨ input = [0])` → the result is `c.length` and `Holds s' dst c`;
  - R3 = for the result `r := result.toInt`, `0 ≤ r` → `r ≤ initDst.length` ∧ `∃ ss last content, ParsesAny input ss last ∧ (Lz4.decode ss []).map (· ++ last) = some content ∧ content.length = r.toNat ∧ Holds s' dst content`, where `ParsesAny` = `Lz4.Parses` with offsets `0 … 65535` (all other parser constraints kept) and no `EndOk`; offset 0 relies on `Lz4.copy` reading `out[out.length]!` = 0 → an explicit `copy_zero` lemma.
  - Shared format vocabulary = `FVATest/Subjects/Lz4/Format.lean` (reviewed for Lz4Wasm); the spec module imports reviewed modules alone.
- Acceptance: `fva trust` PASS on `FVATest/Subjects/Lz4C` (default + `--paranoid`), surface pinned in `scripts/test-subjects`; build + replay time + memory recorded.

## Evidence (E)
- E1 Checkpoint 1 table (M0–M5 per route, raw observations, ruling) appraised by a `scientist` before it steers checkpoint 2 or a `Decisions` entry.
- E2 Vocabulary audit (A1, A2) by a fresh `reviewer` against Wasm 2.0 §4.4.7 + the `Step` rules: every successful guest load/store rule has its case; contexts match `Step`'s; scope statement accurate. Findings → `.agent/review.md`.
- E3 A4 negatives, each red on its planted input, recorded in the commit body.
- E4 Groundwork costs (instance, footprint seam, manifest/mutation updates) recorded apart from route costs.

## Out of scope
- Encoder (`LZ4_compress_default`), lz4_flex (T3), partial decoding + dictionaries (unreachable from `LZ4_decompress_safe`), D9's per-block evaluator and an automatic decompiler (out of U19's session; IMPLEMENT's method choice = U20), a source-release/compiler-version transition (fvapi's version-proof economics; M4 is an optimization perturbation only).

## Status (MAIN)
- Seam built: A1 `FVA/Spec/Exec/Access.lean` (`Reads`, `Writes`, `Within`, `Throughout`) + A2 `CallWithin` (`CAbi`, with `InvokeOK`); A3 `FVA/Impl/Exec/Access.lean` (`access`) + `FVA/Proof/Exec/Access.lean` (`reads_iff`, `writes_iff`) + `FVA/Proof/Lib/Footprint.lean` (`MustW`, `Until`, `mustW_of_until`, `Until.trans`/`mono`, `wasm_access` simp set, tactics `wasm_cstepw`, `wasm_cstepu`, `wasm_within`); `Context` + `blockCode` & co. moved from EdgerCpm into `FVA/Proof/Lib/Context.lean`; `Det.lean` gained `no_step_values`, `steps_values`, `no_step_trap`, `no_step_final`, `final_unique`, `Must.outcome` (moved/added once). A4 `FVA/Proof/Lib/FootprintExamples.lean`: positive + rejection `CallWithin` for a callee-frame store and load; planted checker bound `+1` and deleted `Reads.frame` both break `FVA/Proof/Exec/Access.lean` (recorded in `.claude/rules/fva-checks.md`). A5 `FVATest/Subjects/Lz4C/`: `Lifted` + NOTICE, `instance_eq` (every fresh instance = one store: data segment by kernel-run `runDet` + `Must.outcome`), `Code` slices checked against `Lifted.func2` (`extLoop_eq`).
- E2 = reviewer-1: V1–V8 pass, 0 findings (cross-checked against the Wasm 2.0 PDF §4.4.7).
- Checkpoint 1 = L1 holds (`Ext.lean` `ExtL1`, frozen sha256 3466d1aa…): proved by route D (`ExtDirect.ext_l1`) and route R (`ExtRefine.ext_l1`); M4 `-O1` perturbation (`lz4-c-O1.wasm`, 11,167 B; loop 33 vs 22 instructions, renumbered locals, pre-incremented pointer, error flag + shared exit) proved by both (`O1/ExtDirect`, `O1/ExtRefine`, statement `O1/Ext.lean` `ExtL1O1`); the four historical exports contain only the standard axioms and were accepted by leanchecker + con-leche; final-source acceptance after the shared-helper extraction recorded separately (commit body). E1 (scientist-1 appraised; bounded wording adopted): no Pareto-dominant route (each phase's second implementation was quicker, with documented copying; route and carryover effects inseparable; M2 + M3 without 2× separation) → inconclusive, route D provisionally by policy, not a scaling result. Machine-facing iteration/induction proofs hold most route-specific lines (D 74.7 % / 76.1 %, R 61.0 % / 63.7 % at -O2 / -O1); on -O1 both routes wrote new iteration proofs, reusing the property, common lemmas, D's sum helpers and R's model.
- Checkpoint 2 not attempted in U19's session (gate below); done in the IMPLEMENT phase that followed (method = U20, `docs/contracts/U20-proof-scaling.md`): R1–R3 proven, `fva trust` PASS in both modes in the full gate — results at the end of this section.

### Checkpoint 2 obligation inventory (func 2 + callees, `-O2`)
| # | class | where | status |
|---|---|---|---|
| I1 | entry guards, zero-capacity `select`, end-pointer setup (straight line) | func 2 head | generic machinery available; target transfer untested |
| I2 | one-byte length extension with bound + overflow guards, two exits | literal `loop @10`, match `loop @8` | literal extension proved (L1, two routes, two builds); match extension untested |
| I3 | byte tail copy (≤ 2 iterations on real paths) | `loop @7` | untested (similar shape to I2) |
| I4 | separate ordered-copy contracts for the compiled `memcpy` and `memmove` shims (bounds, framing, termination, footprint, call composition under a symbolic caller; forward-overlap repetition ≠ `memmove`'s source-preserving result) | func 3 (10 call sites), func 4 (1) | new |
| I5 | loops whose body calls `memcpy` (`LZ4_wildCopy8`) | three wildcopy loops | untested composition (needs I4) |
| I6 | offset < 8 path reading `inc32table`/`dec64table` from the data segment | after `_copy_match` | new (table bytes by kernel evaluation of `store0`) |
| I7 | main-loop invariant ↔ LZ4 format: `dst` prefix = `Lz4.decode` of the parsed prefix, `ip` at a sequence boundary, the 16/18-byte shortcut, last-sequence detection (MFLIMIT/LASTLITERALS margins) | `loop @5` | new (dominant) |
| I8 | R3 converse: a non-negative return ⇒ the input parses (`ParsesAny`, offset 0 as zero bytes via an explicit `copy_zero`) | every accepting path | new |
| I9 | R1 ranges for speculative reads/writes (16-byte literal read, wildcopy over-write ≤ `oend − 5`) | shortcut + wildcopy | new (machinery established) |
| I10 | main-loop termination (`ip` grows) + error returns `−(ip − src) − 1` | all paths | generic machinery available; untested |
| I11 | claim assembly: `Prepared` (src + dst writes), `InvokeOK`, `CallWithin` + `CallReturns` from `MustW` | top level | machinery established, untested at top level |
- Gate result: I4–I9 (and the target transfers of I1–I3, I10, I11) lack a demonstrated pattern ⇒ checkpoint 2 is not started in this session (contract gate) — unmet readiness, not a failed decoder proof or a time bound. IMPLEMENT first: a minimal I4 call-summary composition while scoping an I7 one-sequence semantic invariant, measuring first-use vs reuse effort, export/replay growth and theorem coverage (scientist-1 E4).

### Checkpoint 2 results (IMPLEMENT, U20–U25)

- Claims: `FVATest/Subjects/Lz4C/Spec.lean` R1–R3 over `Call.lean`'s `Buffers` (domain: both buffers in 131072…2097151, lengths < 2^31, disjoint unless one is empty) and `OnCall` (a prepared fresh instance exists; every one); proofs `Proof.lean` (`r{1,2,3}_holds`), never read. `fva trust` PASS default + `--paranoid` in the full gate (`scripts/test-subjects` → `scripts/subject-matrix`), review surface 76 lines (Spec 29 + Call 15 + `Lz4.Format` 26 + `Lz4.Any` 6). R1 = D52's acceptance (`CallWithin` on a lifted subject, trust PASS).
- Observation boundary: R2/R3 = a success's decoded prefix + length; R1 = the call's footprint + termination with one i32. No claim on the exact negative code, on rollback, or on destination bytes past the decoded content (`Model.lean` drops them; consultant-10 P3, accepted).

#### Coverage ledger (a repair index: statement → proof root → focused check)
| row | obligation | status | statement | proof | focused check |
|---|---|---|---|---|---|
| I1 | entry guards, zero-capacity select, end pointers | proved | `Seg.Entry` | `Cut/Entry.lean` `Cut.entry` | `lake build FVATest.Subjects.Lz4C.Cut.Entry` |
| I2 | literal + match length extension | proved | `ExtL1B` (→ `SegA`), `Seg.SegC` | `ExtDirect.lean` `Direct.extL1B`; `Eval/SegC.lean` `Eval.segC` | `lake build …Cut.ExtB …Eval.SegC` |
| I3 | byte tail copy | proved | inside `Seg.SegD` | `Eval/SegDLoops.lean` | `lake build …Eval.SegDLoops` |
| I4 | `memcpy` / `memmove` ordered-copy contracts | proved | `Copy.MemcpyS1`, `MemmoveS2` | `Eval/S1.lean`, `Eval/S2.lean` | `lake build …Eval.S2` |
| I5 | wildcopy loops calling `memcpy` (3) | proved | `LitWildS3`, `MatchWildS4`, inside `SegD` | `Eval/S3`, `S4`, `Wild` (`wc_until`) | `lake build …Eval.S4` |
| I6 | offset < 8 tables | proved | `Seg.TablesOK` | `Top.mem0_tables` (kernel), `Eval/SegDPrologue.lean` | `lake build …Eval.SegDPrologue` |
| I7 | main loop ↔ LZ4 format | proved | `Sim.iterSim`, `loopSim` | `Sim.lean`, `Prefix.lean`, `Match.lean`, `ModelProof.lean` | `lake build …Sim` |
| I8 | R3 converse | proved | `Model.decode_sound` + `Top.r3_of` | `ModelProof.lean`, `Top.lean` | `lake build …Top` |
| I9 | speculative read/write ranges | proved | the cutpoint footprints (`Within`) | every cutpoint proof | `lake build …Eval.Accept` |
| I10 | termination + error returns | proved | `Sim.loopSim`, `Seg.ErrRet` | `Sim.lean`, `Cut/ErrRet.lean` | `lake build …Cut.ErrRet` |
| I11 | claim assembly | proved | `Spec.r1`…`r3` | `Top.lean` → `Proof.lean` via `SpecEq.rk_iff` | `fva trust` (gate) |
| R1 | footprint + termination | proved | `Spec.r1` | `Proof.r1_holds` | `scripts/test-subjects` |
| R2 | valid block → decoded length + bytes | proved | `Spec.r2` | `Proof.r2_holds` | same |
| R3 | non-negative result → parse + bytes | proved | `Spec.r3` | `Proof.r3_holds` | same |
Supplementary counts: func 2's body (550 static instructions) = the proven cutpoint slices Entry, S5, SegA–SegD and ErrRet, which `Top`'s composition joins into every path from the entry to a return; funcs 3/4 (93 + 191) = S1/S2; call sites 11 / 11 (10 × `memcpy`, 1 × `memmove`) composed through S1/S2.

#### First-use vs reuse effort (new + changed code lines, authoring minutes M0; engine C unless noted)
| piece | first use / reuse of | lines | M0 min |
|---|---|---|---|
| S1 `memcpy` | first use (engine + contract) | 511 | 33.8 |
| S2 `memmove` | reuse of S1 (2.05× the instructions) | 633 | 43.3 |
| S3 literal wildcopy | first composition with S1 | 113 | 5.0 |
| S4 match wildcopy | reuse of S3 | 26 | 1.0 |
| S5 shortcut | S1 ×4 + branch joins | 368 | 34.1 |
| SegC match-length loop | first data-dependent loop | 247 | 22.8 (contended) |
| SegB general literal path | reuse of S2 + S3 | 203 | 25.8 (contended) |
| SegD offset/match path | reuse of S1, S4, `wc_until`, SegC support | 655 | 58.75 (contended) |
| SegA via ExtL1B (stepping) | reuse of checkpoint 1's loop proof | 251 + 377 | — |

Shared loop: `ExtDirect.one_iter` + `iter` prove `ExtExitB`; `Direct.extL1B` keeps its exact
bound position and `Direct.ext_l1` weakens it to the frozen `ExtL1`. Historical checkpoint-1
route D = 281 code lines (M1); the current tokenizer counts its pre-extraction module as 282,
its shared proof + weakening adapter as 287 (312 → 319 physical lines). `Cut/ExtB` = composition
alone: 236 → 4 code lines (251 → 9 physical), replacing its repeated iteration/induction proof.
These source counts are separate from the historical effort + runtime measurements above.

#### Export + replay growth
| closure | export | leanchecker | con-leche |
|---|---|---|---|
| frozen statements alone (baseline) | 45.0 MB | 6.8 s | 9.2 s |
| S1 | 126.2 MB | — | — |
| S1–S5 | 146.0 MB | 52.4 s | 60.4 s |
| full decoder (trust closure: R1–R3 + `decode_eq` + bundle) | 202.2 MB | 93–112 s | 39–55 s |
Paranoid on the full decoder: leanchecker-paranoid 122 s, nanoda 46 s, con-ron 38 s accept; lean4lean declines (its recursion limit at `instrStep_sound`). Timings = one shared laptop / pool host, observations only.
