# U30 contract — D51 route pick (research unit; tier: docs — a binding ruling over measured evidence)

Deliverable = the `Decisions` D51 ruling + U31's route–subject pair. Evidence = four rounds of builds + measurements (plans v2 → v4.1, frozen before each round's first build; a change after a build = version bump + regrade), each round appraised by a `scientist` before its ruling.

## Ruling
- Route = J2Wasm (J2CL's WasmGC backend, `google/j2cl@3472ba92`, Bazel, offline from a frozen closure). TeaVM 0.16.0 screened out (its start function calls `teavmJso.createFunction1`: a JS function built from source = a JavaScript-runtime service, no admissible standalone host); GraalVM Web Image desk-excluded (its docs: the module depends on JavaScript-provided imports and runtime).
- Subject = `java.lang.Integer.reverse(int)` of J2CL's JRE emulation at 3472ba92 (`jre/java/java/lang/Integer.java:171–181`, its table `ReverseNibbles.reverseNibbles` `:51–57`), unchanged, exported through the forwarding wrapper `fva.u30.R1.reverse(int value) { return Integer.reverse(value); }` (entry point `fva.u30.R1#reverse`, `jre.classMetadata=SIMPLE`).
- Artifact `r1.wasm` = 346 B, sha256 `414c14fe9977f7944ad5c1c8803426c95862424a361ba274afa3d0f697283ca9`: no import, no start function, no memory; export `reverse (i32) → i32`.
- Grounds (pre-registered decision rule): R1 = the only round-4 candidate meeting E1–E6; the user's rulings fix the rest (below).

## User rulings (verbatim)
- D51 (earlier): aim at Java via WasmGC.
- Round 2 → "Function without errors": an unchanged Java function that never throws (S1 `IntMath.gcd` needed a JS-string host import on its error path).
- Round 3, Q1 (all six eligible candidates compiled to core Wasm, no GC construct) → "The proof must use GC". Q2 → "I choose option 2 for question 1, so I think this question is now irrelevant".

## R1 = the artifact (`wasm-tools print`, full module)
- Types: `rec { 0 = array (mut i32), 1 = struct (field (ref 0)), 2 = func }`, 3 = `func (param i32) (result i32)`; globals 0 `(mut (ref null 1))` = `ref.null none`, 1 `(mut i32)` = 0 (init flag); data segment 0 (passive) = the 16 little-endian `i32` nibble reversals `0 8 4 12 2 10 6 14 1 9 5 13 3 11 7 15`.
- func 1 (ReverseNibbles' class initializer): `global.set 1 ← 1`, then `array.new_data 0 0` (offset 0, 16 elements) → `struct.new 1` → `global.set 0`. The flag is set before the table exists ⇒ `flag ≠ 0 ⇒ table built` holds at export entry + after func 1 returns, not at every intermediate state (scientist-2: phased initializer proof).
- func 0 (`reverse`, locals `(ref 0)` non-defaultable + `(ref null 1)`): `global.get 1; i32.eqz; if call 1 end` (lazy init), then straight line: `global.get 0; local.tee 2; struct.get 1 0` + 8 × `array.get 0` at indices `(x >>> 28)` and `(x >> 4k) & 15` (k = 1…6) and `x & 15`, each shifted + or-ed (the optimizer reordered the source's terms); local 1 set by `local.tee` before its first `local.get`.
- Reach (M3, scorer v4): core 77, `array.get` 8, `array.new_data` 1, `struct.get` 2, `struct.new` 1; nothing beyond P′ + GC; rec group 3, subtype depth 0, no struct/array mutation, 2 allocations (initializer), no loop, dispatch or exception. M7: validates under P′ + `gc`, no further feature.

## Protocol (common to the rounds)
- Metrics: M1 offline build from the frozen closure; M2 host contract (H0 = every function import a trapping sentinel with a counter; R1 has none); M3 feature reach (a: whole artifact, b: execution closure incl. initializer + `ref.func` targets, c: GC proof shape); M4 size; M5 byte-repeatability over two fresh roots (+ MAIN's replay of one root); M6 finite agreement; M7 `wasm-tools validate` 1.262.0 feature minimality; M8 pin closure (offline replay).
- Eligibility (plan v3.1 + v4.1): E1 unchanged (body + callee + initializer ledger, wrapper = forwarding only, i32 ABI); E2 total (source audit + JVM run without exceptions); E3 standalone (no import call in the call + initializer closure, no start, instantiation observed, sentinel counters 0); E4 agreement with both oracles on every frozen case; E5 M7 = P′ + gc; E6 GC use: (a) the export's reach retains a GC array/struct type + a GC access on it, (b) every normal return dominated by such an access on the call path (initializer-only GC fails), (c) cold (fresh instance) + warm (reused) runs reported apart, (d) U31's proof discharges the table invariant over the same bytes.
- Oracles: an independent Python formula per target + the pinned JVM (OpenJDK 21.0.9) running the same forwarding wrapper.

## Rounds
| round (plan) | candidates | outcome |
|---|---|---|
| 2 (v2) | TeaVM, J2Wasm × S1 `IntMath.gcd(int,int)`, S2 `LongMath.gcd(long,long)` (Guava 33.8.0-jre) | TeaVM screened out (start needs a JS service); J2Wasm S1/S2 agree on every nonnegative case (1,110 / 1,157), every negative case traps at the `wasm:js-string concat` sentinel (the guard builds its message before throwing) → user: "Function without errors" |
| 3 (v3.1) | J2Wasm × T1 `IntMath.mean`, T2 `Integer.numberOfTrailingZeros`, T3 `IntMath.saturatedAdd`, T4 `Integer.bitCount`, T5 `IntMath.isPowerOfTwo`, T6 `Integer.highestOneBit` | all six meet E1–E5 (78,198 cases agree); all six validate with every optional feature off = core Wasm → user: "The proof must use GC" |
| 4 (v4.1) | J2Wasm × R1 `Integer.reverse(int)`, R2 `Long.reverse(long)`, control C0 `Integer.reverseBytes(int)` | R1 meets E1–E6; R2 fails the frozen zero-import screen E3 (its export needs a scalar long-box host bridge: 3 imports `goog.math.Long.{getLowBits,getHighBits,fromBits}` at an `externref` ABI; no finding about Java `long` or a need for a JS engine); C0 = no GC (E6's planted control) |

Screened before round 4's builds (plan v4.1, scientist-2's V3 reject adopted): autoboxing/varargs wrappers over Object APIs (one family: Guava `Objects.equal`/`hashCode` delegate to the JRE) = an adapter boundary — an `Integer`-only fixed-arity specialization of an Object API plus added heap work — never built without a user ruling on that boundary (`plan-v4.md`).

## Round 4 evidence (R1)
| check | result | where (base `.scratch/lwr/u30/`) |
|---|---|---|
| M1 + M5 | A4 + B4 fresh offline roots rc 0; r1/r2/c0 byte-identical (A4 = B4) | `spike-j2wasm/deliverable-v4.md` W2–W5 |
| M5 MAIN replay (fresh root M4) | closure-v4 pin checks + `offline-build-v4` rc 0 (2,566 s, 1.98 GB, 1,134 actions); r1/r2/c0 `cmp` = A4 (r1 sha256 414c14fe…) | `m6/v4/replay-M4.{sh,log,time}` |
| E1 | wrapper + `Integer.reverse` + `ReverseNibbles` bodies = the pinned tar's; 28 prepared bodies + 4 fields reproduce their pins | `spike-j2wasm/ledger-v4`, scientist-2 |
| E2 | source: 8 table reads, indices `x >>> 28` / `(x >> 4k) & 15` ∈ 0…15 for every x, no loop, no throw; JVM 2,538/2,538 returns | `r4src/…/Integer.java`, `m6/jvm-v4/` |
| E3 | 0 imports, no start, instantiates | `m6/v4/stats-R1.json` |
| E4 | cases-v4 (seed 20261113): 1,269 per target = every nibble value in every position (121 after dedup) + boundary 148 + 1,000 random; R1 fresh 1,269/1,269 agree; one interleaved instance (1 cold + 1,268 warm calls) rc 0; Python = JVM on all 2,538 rows (`cmp` rc 0); controls fire by class (wrong expected → disagree, trapping export → other-trap, trapping start → setup-trap) | `m6/v4/{cases.jsonl,run-m6.log,fresh-*.jsonl,inter-*.jsonl}` (cases sha256 c903d405…, scorer v4 sha256 8bbb05e4…) |
| E5 (M7) | P′ + `gc`, nothing further | `m6/v4/stats-R1.json` |
| E6 (a)(b) | first top-level GC access = `struct.get` (op 7 of 82), no exit before it; C0 rejected; plants: straight-line → pass, untaken-branch / initializer-only / early-return → fail | `m6/v4/e6-{R1,C0}.json`, `m6/v4/e6-plants.log` |
| scientist-2 (results) | 7 rows: 5 sound / 2 change / 0 reject, both changes adopted (W4 lifecycle counts as stated above; W6 R2 wording); E6 = a narrow top-level syntactic sufficient test for this artifact's shape, not a general CFG verifier | `sci2/results-v4-verdicts.md` |

## Claim target for U31 (provisional; universal level never claimed here)
- For every `x : BitVec 32`: `r1.wasm` decodes, validates + instantiates with no imports (proven, not assumed); calling `reverse` on a fresh instance with `[.i32 x]` returns `[.i32 (x.reverse)]` (bit reversal), terminating; GC allocation of the 16-element array + the struct succeeds (resource assumption stated in the claim text).
- U31 states the lifecycle its theorem quantifies over (fresh instance; a reused-instance corollary = the initialized state, its flag + table invariant).
- Not claimed: JVM or source equivalence, Java exception behavior, reused instances beyond the stated corollary.

## U31 obligations
- Base (shared, reported apart from the per-subject surface): P″ = P′ + the Wasm 3.0 GC classes (`gc-types`, `bottom-types`, `gc-instructions`) at spec pin `859d3232` — syntax, binary grammar + verified decoder, validator + soundness extension, execution (stepper + machine) with a heap of structs + arrays; conformance = `step0/manifest.md` v1.1: 21 official scripts of testsuite@44f1503f, 1,643 commands, one named exclusion (`struct.wast`'s text `assert_malformed`), pinned with 0 FAIL.
- Subject: the phased initializer (flag first, then table), the table invariant (16 constants from data segment 0, no write in reach), the straight-line identity (8 lookups = 32-bit reversal), termination.
- First milestone (reopen gate): r1.wasm decoded + validated + instantiated by FVA; one heap-typing preservation lemma (store extension by a struct allocation); the symbolic normal path for every x; representative exports replayed by every kernel at the gate's limits. Reopen on an unsupported feature, a host requirement, an unsatisfiable init/resource assumption or a proof/replay resource limit.
- Repository contents: `r1.wasm` = an FVA-built example linking third-party code ⇒ rebuilt by a committed script from the pinned closure (v4: 32,224 pins, SHA256SUMS 63daa74b…) published on `veriformatics/fva-artifacts`, emitted-byte hash checked; never committed.

## Teammates
- builder-1 (TeaVM), builder-2 (J2Wasm, round 2), builder-3 (round 3), builder-4 (round 4): builds + ledgers, no scoring.
- scientist-1 (plan v2: 2 sound / 11 change / 1 reject, all adopted); scientist-2 (plan v3: V3 sound, 5 change, V5 reject, all adopted; results v3: 3 sound / 4 change / 1 reject, adopted; plan v4: 1 sound / 4 change / 2 reject, adopted; results v4: 5 sound / 2 change / 0 reject, adopted).
- consultants 15–17 (ruling v2: R2 + R5 sound ×3, the rest change, 0 reject; adopted).
