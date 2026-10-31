# consultant-1 — U19 contract verdicts

Direction = right: access-level claims + a compiled-loop comparison address the unshown guarantee. Contract needs correction before either route is frozen. Verdicts = 1 pass / 7 fix / 1 risk; every target row adjudicated. This is a contract review, not verification of the planned implementation.

Root `P` = `/home/eturkes/Projects/fva`; source citations below are `P`-relative unless absolute. WAT = `.scratch/u19/wat/lz4-c.wat`; C = `.scratch/u19/src/lz4-1.10.0/lib/lz4.c`. Draft reviewed = `docs/contracts/U19-decoder-spike.md`, lines 1–41. Source edits by MAIN occurred during the review; relevant final anchors below use the observed current files, except where a baseline is named.

| id | check | verdict (pass / fix / risk) | evidence (file:line or source excerpt) | recommended change |
|---|---|---|---|---|
| K1 | A1 exact redex + contexts, traps/branches/returns | pass | `FVA/Spec/Exec/Step.lean:441–449`: `seq` preserves a **value** prefix, `label` evaluates its body, `frame` uses the inner frame. `:393–400,450–453`: branch/return/trap discard continuations without reducing their loads. Packed-read context experiment passes, rc 0 (§K1). | Keep contexts verbatim; include every memory-rule premise and half-open byte interval. Freeze store-address identity, not just the frame's memory index. |
| K2 | A1 every semantics-level memory access | fix | `Step.lean:247–284`: successful load/store rules call `read`/`write`; `:305–368`: bulk operations expand through packed accesses. `:289–296,427–434`: growth/host outcomes change memory without such a redex. Precedent `Proofs/MemorySpec.lean:23–32` counts attempted accesses + whole bulk ranges instead. | State the vocabulary's scope = successful guest load/store **byte accesses**, not all store effects. Revise E2's “every memory-touching rule” and do not copy the precedent's extractor unchanged. §K2. |
| K3 | A2 non-vacuity + faithful combination with CallReturns | fix | `FVA/Spec/Claims.lean:75`: existing calls require `InvokeOK`; draft A2 only says export resolves. `FVA/Spec/CAbi.lean:26–27,100–101,114–120`: existence/preparation witnesses prevent empty-instance/buffer domains. | Add `InvokeOK` to `CallWithin`; explicitly quantify the same prepared invocation in footprint + return claims and witness its existence for every allowed input/destination. Safety alone intentionally admits a wrong/stuck/divergent program. §K3. |
| K4 | A3 checker + within_of_walk, choice points | fix | `FVA/Proof/Lib/Walk.lean:19–23`: `walk 0 c = some c`; `:39–42`: existing transport requires a tail `Must`. `FVA/Proof/Exec/Det.lean:232–234`: `step_complete` requires `uniqueStep c = true`. Kernel counterexample: a zero-length safe prefix does not imply `Throughout`, rc 0 (§K4). | `throughout_of_walk` needs a safe tail or a no-successor endpoint; otherwise conclude prefix safety only. `wasm_step1w` must transport a goal that actually contains safety. Choice points need branchwise treatment, not one reference outcome. |
| K5 | A4 negatives fire | fix | `FVATest/Examples/Mem/Lifted.lean:27–34`: `call_scale` and its sole callee contain arithmetic/calls alone; no loads/stores. Kernel equality check passes, rc 0. `FVATest/Mutate/config.json:38–39,46–49`: mutation scope = implementation + reached spec helpers, not `reads_iff` proof text. | Replace `call_scale` with an explicit nested-frame load/store **positive access witness** + disallowed-access rejection. Mutate access computation's endpoint, not a proof theorem. No A4 firing is established yet. §K5. |
| K6 | Checkpoint 1 loop + L1 frozen, representative, non-vacuous | fix | WAT `:3888–3904`: locals 18/2/3 and final `br 2 (@5)`; draft `:18` combines arbitrary continuation with unbounded `Throughout`. C `:2422–2429` + constants `:244–245` bound the reachable byte tail to ≤2 bytes. | Use a total-until-exit judgment, fix the exact enclosing labels/exit and local/memory bindings, and bind the slice to `Lifted.func2`. Call the loop a generalized overlap-copy microbenchmark, not every near-capacity block's path or a full-decoder scaling proxy. §K6. |
| K7 | R1–R3 vs task requirements | fix | `bench/tasks/lz4-c/README.md:14–18` matches draft requirements in substance. `FVATest/Subjects/Lz4/Format.lean:38–61` implements independent matches + end conditions. Draft `:29` leaves `content` free; signed sizes/results and buffer preparation remain prose. Kernel offset-0/overlap/empty-block checks pass, rc 0 (§K7). | Close the binders/types: signed i32 result, Nat lengths/ranges, existential `content`, prepared input/destination + existence. Keep R2's special capacity clause and R3's two stated departures exactly. |
| K8 | Session bound + stop rule honest/decidable | fix | Draft `:21–22,32` leaves M4's two coordinates unranked, “≥2×” direction ambiguous, “sustained attempt”/“fits it” unmeasured; M2 is elaboration cost, not proof-authoring cost. `.agent/spec.md:56,63` asks for the full all-input theorem as checkpoint 2. | Freeze an executable route-ranking rule + explicit remaining-effort/gate reserve before measurements. M5 = heuristic/lower-bound information only. Checkpoint-1-only close = partial/inconclusive, never the full spike's pass. Routing/waiver needs the user's ruling. §K8. |
| K9 | Instantiation, summaries, costs, manifest + mutation | risk | WAT `:5–6,4365`: fixed 32-page memory, initialized global, active data segment; `FVA/Proof/Lib/Instance.lean:33–35,49–50` requires empty globals/data. `docs/contracts/U8-library.md` Status explicitly leaves L6 summaries + writes/frames + globals/data as first-consumer work. Mutation graph excludes all subjects (`config.json:3–4`). | Front-load initialization/existence, real callee footprints and symbolic memory frame lemmas; wire the verified checker into proof roots/self claims/tests; regenerate the base manifest + mutation table. Budget these costs separately from route M1–M5. §K9. |

## K1

A1's design is sound at the reduction-context level. `Step.seq` is `vals vs ++ es ++ rest`, not an arbitrary-prefix search (`FVA/Spec/Exec/Step.lean:441–443`). Thus a load after `nop`, `br`, `return`, a pending trap or any other non-value cannot be selected before that instruction. The label/frame constructors inspect `body`, never `cont` or `rest`, and the frame case changes the active frame to `fi` (`:444–449`). These constraints preserve the memory selected by the actual redex.

Minimal packed-read prototype: `/home/eturkes/Projects/fva/.scratch/u19/consultant-1/FootprintContexts.lean` defines the proposed packed-load case + exactly those three contexts and proves `ProbeReads c ma a → ∃ c', Step H c c'` by induction. Command from `P`:

```
systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 \
  lake env lean /home/eturkes/Projects/fva/.scratch/u19/consultant-1/FootprintContexts.lean
```

Output: `"PASS: proposed packed-read contexts always witness a real Step"`; rc 0. Coverage = packed reads + context construction only; this is not `reads_iff`, an implementation audit or an exhaustive proof over all memory cases.

## K2

Replacement A1/E2 scope text:

> `Reads`/`Writes` record successful linear-memory byte accesses performed by the four guest load/store redex rules, including accesses in nested frames and accesses reached after bulk-instruction expansion. Trapping accesses perform no byte read/write. They are not predicates for every change to a memory store. Allocation/growth and host outcomes have separate effects; this decoder's reachable code has neither growth nor host calls. E2 classifies every rule into direct byte access, expansion, no byte access, or an explicitly excluded effect.

Reason: `Step.memoryGrow` sets a new `MemInst` (`FVA/Spec/Exec/Step.lean:289–293`); `MemInst.grow` initializes appended bytes (`FVA/Spec/Exec/Runtime.lean:223–226`). Host outcomes may supply **any** new store permitted by `H` (`Step.lean:427–434`). Neither reduces through `loadPacked`/`storePacked`. A generic theorem “bytes outside Writes never change” would therefore be false. No such theorem is required for this import-free fixed-memory decoder; its applicability conditions still need to be explicit.

Bulk memory is correctly covered transitively: `memory.copy` expands to load8/store8 (`Step.lean:328–345`), fill/init to store8 (`:305–312,357–368`). Reading a passive data segment during `memory.init` is not a linear-memory read. An Option holding one next-redex range is sufficient for these rules.

Checker parity requires memory lookup, memory **store address**, bounds, natural-number effective-address addition and `v.numBits`/`v.intBits` checks (`Step.lean:247–279`). The archived `Proofs/MemorySpec.lean:23–32` intentionally ignores those checks and reports whole bulk operations early; it is not an implementation of A1. Its frame traversal also discards the inner frame because it has no store-address/bounds lookup (`:43`). Treat it as a traversal sketch only.

Artifact check: `wasm-tools print bench/subjects/wasm/lz4-c.wasm | sha256sum` and `sha256sum .scratch/u19/wat/lz4-c.wat` both give `009da55f09edb6afa1dbec3598175739fd9b33c6c8ae584f3b28bebe63678a72`, print/hash rc 0. Positive control: WAT `^  \(memory ` count = 1, rc 0; WAT `^  \(import ` count = 0, rc 1. Thus the cited WAT is byte-bound and import-free. No instruction-reachability theorem was run.

## K3

Replacement A2 core:

```
Throughout H P c := ∀ c', Steps H c c' → P c'
Within R W c :=
  (∀ ma a, Reads c ma a → R ma a) ∧
  (∀ ma a, Writes c ma a → W ma a)
CallWithin H s inst name args R W :=
  ∃ fn, inst.exportFunc name = some fn ∧ InvokeOK s fn args ∧
    Throughout H (Within R W) (invokeConfig s fn args)
```

A byte-only policy remains representable as `fun _ a => ...`; the `ma` parameter prevents silently conflating memory 0 of different instances. In a fresh single-memory subject, prove `inst.mems = [0]` once.

Without `InvokeOK`, an export at a nonexistent function address has no successors/no footprint and satisfies the draft safety form. `CallReturns` closes that hole when conjoined, because it expands through `CallMust` and `Must.next` requires progress (`FVA/Spec/Claims.lean:30–34,75–82`). The shared helper should retain the existing call-form guard itself.

For subject claims, explicitly construct the same `ps = [.write src input, .write dst initialDst]` for both footprint and return statements, with `input.length = srcSize`, `initialDst.length = dstCapacity`, and a prepared-instance existence conjunct `∀ H, ∃ s inst, Prepared Lifted.module H ps s inst`. Then quantify over **every** such prepared instance. `Prepared` and `ReturnsOut` provide the precedent (`FVA/Spec/CAbi.lean:100–101,114–120`). This covers arbitrary initial destination bytes rather than only fresh zeroed memory and avoids vacuity if initialization/preparation is impossible. Conditions asserting a predicate about a post-call state must occur in `CallReturns`'s postcondition for that same call.

Safety remains safety: it allows an in-bounds decoder that returns the wrong answer, or an instruction sequence that gets stuck/diverges without accessing memory. Conjoining total correctness and R2/R3 is necessary and matches the draft's intention.

## K4

Replacement A3 transport:

> A checked finite prefix proves safety only for that prefix. `throughout_of_walk` additionally takes `Throughout H (Within R W) c'` at its endpoint and transports it to `c`; a final/no-successor specialization discharges that tail. At each step, current `Within`, successful reference stepping and `uniqueStep = true` are premises. Choice points are rejected or proved branchwise; one chosen reference trace is not universal coverage. `wasm_step1w` operates on a combined safety/total-correctness goal or a total-until-exit goal whose step rule includes the footprint obligation.

Existing `must_of_walk` has exactly the tail shape (`FVA/Proof/Lib/Walk.lean:39–42`); removing its tail analogue cannot be sound for `Throughout`. `seq_complete` additionally admits the stepper's `.stuck` case (`FVA/Proof/Exec/Det.lean:95–102`); use `step_complete` only after obtaining the successful step it requires (`:232–234`). Pending traps are excluded by `uniqueStep`; the deterministic runner has a separate normalization argument (`FVA/Impl/Exec/Det.lean:49–82`, `FVA/Proof/Exec/Det.lean` `step_traps`/`must_trap`).

Kernel counterexample in `/home/eturkes/Projects/fva/.scratch/u19/consultant-1/ContractChecks.lean:8–20`: `P c := c.instrs ≠ []`; `P [nop]`; zero steps leave it true; one legal `Step.nop` reaches `[]`, so `¬ Throughout H P [nop]`. The source equation `walk 0 c = some c` (`Walk.lean:20`) makes this a direct counterexample to finite-prefix transport without a tail. Command = the K1 command with `ContractChecks.lean`; output `"PASS: finite-prefix counterexample; offset-0 default; call_scale has no memory ops"`, rc 0.

The same defect applies to `Within`: finish a checked prefix before a continuation whose first successful access is outside the policy. That continuation is beyond the prefix, but it remains reachable under `Throughout`.

## K5

Replacement A4:

> Keep a concrete outside-policy store and prove both its reachable `Writes` witness and checker rejection. Add explicit positive `Reads`/`Writes` witnesses under `seq`, `label` and a callee `frame`; dropping each corresponding context must break that witness. Use a callee that actually loads/stores. Mutate `Ref.access`'s half-open range endpoint/length in implementation scope; a theorem or behavioral assertion must fail. Record each exact planted change, clean baseline, failure command, rc and diagnostic.

`call_scale` calls only func 2, whose body is `local.get; const; mul; const; add` (`FVATest/Examples/Mem/Lifted.lean:27–34`). `/home/eturkes/Projects/fva/.scratch/u19/consultant-1/ContractChecks.lean:25–31` kernel-checks both bodies by equality. A missing `Reads.frame` therefore cannot be detected by an access witness for this program. More generally, deleting constructors **weakens** Reads and makes an upper-bound safety theorem easier; a positive access witness/completeness assertion is needed to kill that defect.

`reads_iff` belongs to proofs; the configured automatic mutation groups target `FVA/Impl/Exec` and reached `FVA.Spec` helpers (`FVATest/Mutate/config.json:38–39,46–49`). Mutating the access computation tests the required implementation property. Unconfirmed: none of the new A4 planted failures has run; planned access modules/tests are not the reviewed artifact yet.

## K6

Replacement L1 form:

> Prove total arrival at the exact post-branch exit context for the lifted func-2 slice, with footprint obligations on reductions **strictly before** that exit. Fix the surrounding three labels required by `br 2`, but keep code that runs after the exit symbolic and unevaluated. Bind locals 18/2/3 to unsigned Nat addresses `op`/`match`/`cpy`, require their existence, the active instance memory lookup and successful store lookup, `match < op < cpy`, and in-memory/no-wrap bounds. At exit, `op.toNat = cpy`, `match.toNat = oldMatch + (cpy − oldOp)`, exact sequential-copy memory and unchanged other store fields. Use a proof-side total-until-exit judgment, not unconditional `Throughout` at the entry.

A suitable proof-side judgment has `done : Q c → Until H P Q c` and `next : P c → (∃ c', Step H c c') → (∀ c', Step H c c' → Until H P Q c') → Until H P Q c`. It does not require `P` of an exit whose next instruction belongs to the arbitrary continuation. Its all-successors premise gives total reachability, not merely an existential `Steps` witness. Both routes must prove the same frozen `Until` statement, and a composition lemma attaches an actually safe continuation for whole-call `Throughout`.

Exact control flow: WAT `:3888–3904` loads from local 2, stores at local 18, increments both, tests local 3 and either repeats or executes `br 2 (@5)`. With an arbitrary context that lacks those labels, that branch gets stuck; with a real arbitrary continuation, accesses after it may violate the loop's intervals. Slice identity and enclosing-context identity must be kernel-checked against `Lifted.func2`, not copied into a stand-alone toy program. A concrete reachable-entry witness prevents testing a slice that never runs; it need not prove whole-function reachability for every input before checkpoint 1.

Representativeness correction: C `:2422–2429` uses `oCopyLimit = oend−7`; when the byte loop runs, `op ≥ oend−7` (either it was already there or the preceding wild copy set it there) and `cpy ≤ oend−5`. Thus at most two remaining bytes. This bound was kernel-checked with `omega` in `/home/eturkes/Projects/fva/.scratch/u19/consultant-1/FormatChecks.lean`. C `:2320–2329` final-literals path exits without this match-copy tail, so “the end-of-output path every block near capacity takes” is false.

`match < op` does not automatically exclude the decoder's offset-0 path: C `:2407–2419` first seeds zero bytes and advances `op` by 8; tables `:474–475` have index-0 increments 0. It can enter the later tail with `match < op` even though its original match offset was 0. This is a source-level inference; the compiled reachability/invariant connection remains unconfirmed and must be proved at the full-function boundary.

## K7

R1's allowed-region complements match the task's limited observation interval; granting access below 131072/outside 2097152 is not an R1 weakening. Pairing it with `CallReturns` forbids trapping accesses that A1 deliberately does not count. Initial destination contents must be arbitrary (§K3), including bytes read speculatively within the capacity rather than only already-decoded bytes.

R2 matches task `README.md:17`: `Lz4.Valid` includes positive offsets, decoded-output existence and `EndOk` (`FVATest/Subjects/Lz4/Format.lean:38–61`); keep `(1 ≤ dstCapacity ∨ input = [0])`. R3 correctly omits `EndOk` and permits zero offsets, but must preserve every other parser constraint (two-byte offset `<65536`, match length ≥4, final literal-only sequence). Successful `Lz4.decode` enforces that each offset is at most the then-produced length (`Format.lean:46,51`).

Replacement R3 postcondition:

> On return `vs = [.i32 result]`, let `r = result.toInt`. If `0 ≤ r`, then `r ≤ Int.ofNat dstCapacity` and there exist `ss`, `last`, `content` such that `ParsesAny input ss last`, `(Lz4.decode ss []).map (· ++ last) = some content`, `content.length = r.toNat`, and `Holds s' dst content`.

Types/domain: either quantify signed `BitVec 32` arguments using `.toInt ≥ 0` and their Nat sizes using `.toNat`, or quantify Nat sizes under the i32 representability/range bounds and pass `BitVec.ofNat 32`. Write interval membership as `src ≤ a ∧ a < src + srcSize`/the destination analogue. Define disjointness, endpoint arithmetic and the zero-sized interval convention before code. Avoid a natural-order `r ≥ 0` that is tautological for every bit pattern, including negative return codes. R3's `content` must be existentially bound (missing in draft `:29`).

Offset-0 reliance was checked against the actual reviewed vocabulary: `/home/eturkes/Projects/fva/.scratch/u19/consultant-1/FormatChecks.lean` kernel-proves `copy [42,43] 0 4 = some [42,43,0,0,0,0]`, overlap-1 copying, rejection before the start of output, `Valid [0] []`, and the tail bound. Command = K1 command with `FormatChecks.lean`; output `"PASS: offset-0, overlap-1, pre-output rejection, empty-block validity, tail bound"`; rc 0. `Lz4.copy` currently gets zero from out-of-range `List.get!`; direct `#eval` prints panic backtraces while returning those defaults, so state/prove an explicit `copy_zero` lemma or make the zero case explicit before using it as executable reviewed vocabulary. The kernel semantics itself matches the task.

## K8

Replacement stop/status text:

> Track route status separately: proved / failed obligation / infrastructure blocked / not attempted, with commands and measured effort. Compare only results actually obtained. Checkpoint 1 proves the frozen loop lemma; only checkpoint 2's complete R1–R3 theorem earns the decoder spike's pass. If checkpoint 2 is not attempted or not completed, close with partial/inconclusive evidence and the precise blocker, then obtain the user's ruling on the new session/scope. A loop-only success does not reverse `.agent/spec.md`'s all-input finish line.

Draft M4 is a vector `(changed+added lines, re-proof wall time)`. It has no “lower” value when coordinates disagree; `git diff --numstat` exposes added/deleted lines, not an independent changed-line quantity. The “other route is ≥2× on M1 or M2” exception also leaves whether larger means better/worse unstated. A replacement must name a primary coordinate, exact added/deleted-line convention, inequality direction, tradeoff rule and treatment of a failed M4 proof. The scientist can supply this ranking; it must be fixed before either route runs.

M5 on this loop cannot decide that checkpoint 2 “fits” a session. It lacks distinct obligations: variable-length parsing, error paths, arithmetic/overflow, speculative copies, call summaries, data-segment instantiation and final R2/R3 refinement (§K9). Elaboration seconds are not proof-authoring seconds. Use the projection as explicitly heuristic information and budget scaffolding/gates separately; never turn “17 instructions × ratio” into a demonstrated full-decoder feasibility claim. “Sustained attempt” is not a decidable cap; name the remaining effort/resource budget and its stopping observation before measurement.

## K9

1. **Instantiation is a prerequisite, not a trivial reuse.** WAT `:5–6,4365`: `(memory 32 32)`, mutable global 65536 and a 64-byte active segment at 65536. `instance_alloc`/`instantiable_alloc` require empty globals/data (`FVA/Proof/Lib/Instance.lean:33–35,49–50`). Prove initialized-store facts, successful existence and uniqueness/adequate characterization for every fresh instance; do not substitute a guessed initialized store into the claim. `FVA/Spec/Exec/Instantiate.lean:108–121` runs active segments through `memory.init` + `data.drop`. Decoder table loads at WAT `:3812,3820` depend on segment bytes. Capturing code slices alone is insufficient.
2. **Callee summaries are new proof infrastructure.** `docs/contracts/U8-library.md` Status says “L6 callee summaries … L4 writes + frames, L2 globals + data segments → U14”; the current `FVA/Proof/Lib` files contain no memcpy/memmove summary. `bench/subjects/c-memory.c:3–18` defines forward byte-copy and direction-sensitive memmove. An unconstrained snapshot-style memcpy theorem is false on overlapping inputs for the actual forward-copy code; use sequential copying or discharge non-overlap at each call. Summaries must include termination, exact output/store frame, footprint and contextual composition, not only return values.
3. **Kernel costs need the existing mitigation.** `FVA/Proof/Lib/Walk.lean:142–145,350–359` warns about definitional evaluation of symbolic payloads next to 4294967295. Its `seq`-level propositional rewrites avoid that cost. Access traversal/equation lemmas should follow that route rather than unfold `step`/Option plumbing or recursively expose symbolic `BitVec` values to large Nat literals. The loop comparison cannot charge missing shared infrastructure to just one route.
4. **Build/replay/mutation reachability.** Add the new checker and soundness modules to actual library/proof imports, not merely the filesystem. `FVATest/Mutate/config.json:3–6` excludes every subject, so a subject theorem is not an automatic mutant killer. Include `reads_iff`/`writes_iff` through the `FVA` proof root, checker assertions through an executable test import, and the checker guarantee in the self package if it is to be covered by the existing `fva trust` self-verification claim (`FVA/Self/Spec.lean:1–12,34–46`). Mutants in `Impl/Exec/Access` should be inventoried under the existing `exec` group (`config.json:38–39`); generated tests/proofs must actually kill them. A dropped spec context is a separate planted-spec check if the mutation operators do not visit inductive constructors.
5. **Manifest + budgets.** `scripts/make-base-manifest:15–25` hashes all FVA `.lean` files and fails when stale; add/edit the spec/checker, regenerate once and review the surface/base growth separately. `.claude/rules/fva-mutation.md` requires stale-table updates under the configured memory cap. `scripts/test-subjects` needs the new subject's exact review-surface pin + negatives; default and paranoid replay remain checkpoint-2 acceptance, not a loop-only PASS.

No new implementation/gate run was performed by this reviewer. The artifact's byte count and sha256 were checked directly: 8469 B, `8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6`. All three scratch Lean checks above passed under the 12 GiB no-swap cap. One intermediate rerun through `FVA.Proof.Lib.Walk` failed, rc 1, because MAIN's concurrent rebuild removed `FVA/Proof/Exec/Det.olean`; subsequent checks used stable spec imports and passed. LSP was tried on `Step.lean`: no `.lean` server available. This review makes no claim about full-package build, A4 firing, kernel replay, mutation results, route measurements or full-decoder proof success; each is unrun here.

Recommended next step = MAIN rules K2–K8, edits/freezes the contract + seeded comparison check, then builds the shared seam/initialization once before route D/R work. Keep the finite-prefix distinction explicit throughout.

consultant-1-DONE-1
