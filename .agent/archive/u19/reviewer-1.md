# reviewer-1 — U19 E2 footprint vocabulary audit

Verdict = **pass**; fixed rows adjudicated = **8/8**; findings = **0**. Scope = U19 A1/A2 vocabulary + named checker statements + A4 frame witnesses. Repo sources read-only.

| id | check | verdict (pass / finding) | evidence (file:line + quoted bytes, or experiment + output) | fix |
|---|---|---|---|---|
| V1 | Every successful guest memory-access rule of `Step` (`load`, `loadPacked`, `store`, `storePacked`) has a `Reads`/`Writes` base case whose redex + premises match the rule verbatim (bounds, `mems[0]`, `numBits`/`intBits`, the half-open byte interval) | pass | `FVA/Spec/Exec/Access.lean:22–31,41–50` mirrors `Step.lean:247–279`: memory-0/store lookup, Nat effective address, `t.bytes` / `p.bits / 8`, value compatibility for stores; adds exactly `ea ≤ a ∧ a < ea + n`. | — |
| V2 | The context cases (`seq`, `label`, `frame`) match `Step`'s context rules exactly (value prefix, inner frame for `frame`) | pass | `FVA/Spec/Exec/Access.lean:32–37,51–56` / `Step.lean:441–449`: `vals vs ++ es ++ rest`, label-body descent, `Reads ⟨s, fi, es⟩ ma a` / `Writes ⟨s, fi, es⟩ ma a` use the callee's frame, preserving memory address identity. | — |
| V3 | No case fires at a configuration whose next `Step` reduces something else (pending trap earlier, `br`/`return` unwinding, a load behind a non-value, a trapping out-of-bounds access) | pass | Constructor inspection: only a value prefix may precede a memory redex; label/frame descent enters bodies, never continuations; successful bound premises contradict trap bounds. Capped Lean `Probe.lean` rc 0 checks `access = none` for earlier trap/nop/br/return, nested br/return, OOB load/store; `reads_iff`/`writes_iff` transport each to absence of both footprint relations. | — |
| V4 | The module docstring's scope statement is accurate: bulk instructions only through their expansion steps, trapping accesses/`memory.grow`/host effects are not accesses, and the limitation to import-free modules is stated where a reader of a claim needs it | pass | `FVA/Spec/Exec/Access.lean:6–13` defines an in-bounds load/store footprint, explicitly excludes traps + host effects, names bulk expansion + import-free scope; `CAbi.lean:8` independently states fresh import-free instances. `memory.grow` is not a load/store (implicit, not separately enumerated); probe confirms no access. Official release-2.0 PDF §4.4.7 pp. 97–106 matches scalar access ranges and packed bulk expansions. | — |
| V5 | `Within`, `Throughout`, `CallWithin` are non-vacuous and say what their docstrings say (`InvokeOK`, memory-indexed `R`/`W`, reflexive closure includes the start, safety-only) | pass | `Access.lean:60–65` universally bounds both relations with predicates of `(ma,a)`; `Throughout` uses `Steps := Relation.ReflTransGen (Step H)` (`Step.lean:458`), including zero steps. `CAbi.lean:36–43` requires export resolution + `InvokeOK` before the safety predicate, shares the exact `invokeConfig` with `CallReturns`; does not claim progress/termination/trap-freedom. `Probe.lean` checks start inclusion + export/argument guards. | — |
| V6 | `reads_iff`/`writes_iff` + `Access.Covers` state the intended equivalence (kind, memory, interval); the proofs are kernel-checked, so judge the statements | pass | `FVA/Proof/Exec/Access.lean:17–18,234–251`: `x.write = write ∧ x.mem = ma ∧ x.start ≤ a ∧ a < x.start + x.len`; full `↔`, `false` for Reads / `true` for Writes, same `c`, `ma`, `a`, and `access c = some x`. No omitted field/endpoint or weakened implication. | — |
| V7 | `FVA/Proof/Lib/FootprintExamples.lean` rejections actually depend on frame descent (an access inside a callee frame) and would fail if the spec's `frame` case were dropped | pass | `FootprintExamples.lean:32–34,78–92`: reachable access lies below two `.frame` + two `.label` nodes; rejection projects `Throughout` at that state and applies `writes_iff.mpr` / `reads_iff.mpr`. Capped `WitnessChecks.lean` rc 0 explicitly constructs both footprints using `frame → label → frame → label → base`, checks both positive/negative signatures + standard axioms; current examples source elaborates rc 0. MAIN's planted deletion result accepted as supplied, not repeated. | — |
| V8 | Anything in A1/A2 a claim author could misread so a `CallWithin` claim reads stronger than it is | pass | No guarantee-vs-definition mismatch within A1/A2 scope. `CallWithin` is a safety bound on successful guest byte accesses, not attempted OOB accesses, memory allocation/zeroing, host effects, store equality, or termination; A1 excludes those effects, A2 / `CAbi.lean:39` assigns total correctness to `CallReturns` on the same invocation. `(ma,a)` is a store-memory address + byte, not a module index; probe distinguishes memory 1 from memory 0. The local doc references `Within`; import-free scope is in both vocabulary module headers. | — |

## Verification

Root = `/home/eturkes/Projects/fva`. Every Lean invocation below ran from that root with prefix `systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 lake env lean`:

| Target / check | Result | Evidence |
|---|---|---|
| `.scratch/u19/reviewer-1/Probe.lean` | rc 0 | `probe.log`; excluded redexes, memory identity, upper endpoint, reflexivity, invocation guards; `reads_iff` / `writes_iff` axiom sets = `[propext, Classical.choice, Quot.sound]`. |
| `FVA/Proof/Exec/Access.lean` | rc 0 | `access-source.log`; current source elaborated, not only imported old declarations. |
| `FVA/Proof/Lib/FootprintExamples.lean` | rc 0 | `examples-source.log`; current examples source elaborated. |
| `.scratch/u19/reviewer-1/WitnessChecks.lean` | rc 0 | `witness.log`; direct nested-frame constructors for Reads/Writes, all four example theorem types + standard axiom sets. |
| Verdict validator | 8 rows / 8 pass / 0 unresolved cells | Positive control = one seed line → count 1, rc 0; final report → count 0, normal grep rc 1. |

Initial probe failed during import setup: missing `FVA/Proof/Lib/Footprint.olean`; import-light probe succeeded, and the examples source subsequently elaborated once the dependency was available. First explicit store-witness attempt failed from unconstrained metavariables in the scratch proof; a concrete goal type corrected it. Neither failure is attributed to target behavior.

Not run: full gate, independent-kernel replay, new planted frame deletion (MAIN supplied that result; brief exempts repetition), exhaustive arbitrary-config test enumeration. V1–V3 source reasoning covers the constructors; probes are representative corroboration, not a claimed exhaustive test suite. Lean LSP unavailable (`No LSP server available for file type: .lean`); source reads + elaboration used instead.

## Source anchors

Official [WebAssembly release 2.0 PDF](https://webassembly.github.io/spec/versions/core/WebAssembly-2.0.pdf), §4.4.7, printed pp. 97–106 / PDF pp. 101–110; inspected visually + text-extracted. Distinctive source excerpts:
- Load: `Let ea be the integer 𝑖 + memarg.offset.`; `If ea + 𝑁/8 is larger than the length of mem.data, then:`; `Let 𝑏* be the byte sequence mem.data[ea : 𝑁/8].`
- Store: `Replace the bytes mem.data[ea : 𝑁/8] with 𝑏* .`
- Bulk fill/copy/init execute `i32.store8` / `i32.load8_u` in their expansion rules. Data-segment lookup by `memory.init` is not a guest linear-memory read.
- Alignment note: `The alignment memarg.align in load and store instructions does not affect the semantics.`

PDF sha256 = `960feb141a39a07047b87a27c1dd77adb8a1938bbb114ee2675d9b13de7a7888`. The brief's live HTML URL now serves a later release; W3C text fetches returned HTTP 403 and a guessed multipage release-2 URL returned 404. They did not supply the ruling; the version-fixed official PDF did.

Audited source sha256, stable from initial read through close:
- `FVA/Spec/Exec/Access.lean` = `8299b70c5a42fc4d7b234245c3e15a8e7b9099bd1efc184d69b5224884fb9667`
- `FVA/Spec/CAbi.lean` = `86ff87d7c1f5d8ed066b17bed0ee3891745d10253b0c1686e1d60b154de7feaf`
- `FVA/Proof/Exec/Access.lean` = `bc9c2e6e8b3e3c8f5f75df481cbf2c155527650cbb692354b9193fa2c9be24a6`
- `FVA/Impl/Exec/Access.lean` = `030367565873cf67c2213386f69686b43ca5effc8c3cfe3862cb6aeac77be5f8`
- `FVA/Proof/Lib/FootprintExamples.lean` = `b2a07b20327f0e7c926bfb022ac29c4f2157b17fcdbced97300d880d16bc7f7f`

## Register

None.

reviewer-1-DONE-1
