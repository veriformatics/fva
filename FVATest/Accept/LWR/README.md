# Language + Wasm reach acceptance

Contract = `.agent/spec.md` at `3ed6b3612c38f6165ed0b3393f0d07199cc58bed`, Intent + Decisions,
Language + Wasm reach, plus MAIN's public outcome-protocol and claim-dependency rulings below.
FVA implementation unread. Runner interface = `wasm-tools json-from-wast` →
`.lake/build/bin/fvatest spec <json>`; `FVA_SPEC_OUTCOMES` records one tally row per command.

Run `scripts/test-accept-lwr`. Select a unit with `--group U25|D30|D29|CppEH|D28|D51`.
Use `--record DIR` to retain every command, raw output, rc and wall in milliseconds.
The script returns 0 if all checks pass, 1 for an assertion or pending check, 2 for setup,
and 3 for a crash or execution limit. Pending checks never make a green run.

| Contract id | Checks | Finish line |
| --- | ---: | --- |
| U25 (+ U28a stage case) | 14 | Imports match; false assertions fail; binary malformed means decoder rejection; per-command outcome protocol. |
| U26 / D30 | 5 | Bulk-memory mapping + atomic traps + zero tail; ≥60 KiB copy; `memory_copy 4450 0 0`; full mode executes it; nixbox whole wall <300 s. |
| U28 / D29 | 20 | Six own P' checks, 12 pinned scripts, source hashes, outcome-validator battery; only 13 named text exclusions, no outside skips. |
| U28f / D29 | 3 | Reproducible real-runtime C++ artifact, eight oracle calls, lift. |
| U27+U29b / D29 | 2 | C++ all-input system claim under WASI profile E; trust default + paranoid. |
| U29 / D28 | 10 | Exactly 20 declared WASI imports; four oracle scenarios; four matching `fva run` scenarios; bustools proof seam. |
| U31 / D51 | 2 | Unchanged Java function's all-input claim + trust, and the selected WasmGC route's official conformance. |
| Total | 56 | 21 own WAST files (144 distinct commands, plus a 4-command protocol replay), 12 official files (366 commands), eight C++ calls, four WASI scenarios. |

## Commands and oracles

`R(F)` below means:

```sh
.tools/bin/wasm-tools json-from-wast F -o TMP/ID.json --wasm-dir TMP/
FVA_SPEC_VALIDATE_ONLY=0 FVA_SPEC_OUTCOMES=TMP/outcomes.tsv \
  timeout 180s nice -n 10 .lake/build/bin/fvatest spec TMP/ID.json
```

The suite pins zero failures and zero skips for own positive fixtures. A planted false assertion
must produce exactly one failure, rc 1, with no skips. The time limit is a runner safety limit,
not a proof or a D30 performance result. Set `FVA_ACCEPT_CASE_TIMEOUT` for a longer diagnostic run.

Own-fixture oracle command:

```sh
.tools/bin/wasmtime wast -W exceptions=y,tail-call=y,function-references=y,gc=y F
```

All own positive files return rc 0. The deliberately false fixtures under `planted/` return
rc 1, except `u25-malformed-invalid.wast` (rc 0; oracle limitation below). This is expected:
the planted assertions must be rejected, not made valid.

Official scripts are unmodified Apache-2.0 source at
`WebAssembly/testsuite@44f1503f98409fa3737437bf9449a37a5def4210`, with source paths in `official/NOTICE`
and byte hashes in `official/SHA256SUMS`. Their oracle adds `--ignore-error-messages`; all 12
then return rc 0. This relaxes diagnostic substring matching only. The assertions, modules,
expected values and FVA counts stay unchanged. Without that option, `throw.wast:52` returns
rc 1 because it expects `instruction requires [i32] but stack has []` while Wasmtime prints
`expected i32 but nothing on stack`; `try_table.wast:367` returns rc 1 because it expects
`unexpected token` while Wasmtime prints `attempted to parse a wasm module with a component parser`.

### U25 — each input's baseline output

`p/f/s` = the runner's pass/fail/skip row. All rows below were observed on FVA `3ed6b36`.
A green baseline control is not a mutation-qualified new test.

| Check | File relative to this directory (`R(F)`) | Commands | Oracle rc | Baseline p/f/s; rc | State |
| --- | --- | ---: | ---: | --- | --- |
| U25.function-false | planted/u25-function-false.wast | 3 | 1 | 3/0/0; 0 | RED |
| U25.function-true | u25-function-true.wast | 3 | 0 | 3/0/0; 0 | green control |
| U25.global-false | planted/u25-global-false.wast | 3 | 1 | 3/0/0; 0 | RED |
| U25.global-true | u25-global-true.wast | 3 | 0 | 3/0/0; 0 | green control |
| U25.memory-false | planted/u25-memory-false.wast | 3 | 1 | 3/0/0; 0 | RED |
| U25.memory-true | u25-memory-true.wast | 3 | 0 | 3/0/0; 0 | green control |
| U25.table-false | planted/u25-table-false.wast | 3 | 1 | 3/0/0; 0 | RED |
| U25.table-true | u25-table-true.wast | 3 | 0 | 3/0/0; 0 | green control |
| U25.malformed-false | planted/u25-malformed-false.wast | 1 | 1 | 0/0/1; 0 | RED |
| U25.malformed-true | u25-malformed-true.wast | 1 | 0 | 0/0/1; 0 | RED |
| U25.module-false | planted/u25-module-false.wast | 3 | 1 | 3/0/0; 0 | RED |
| U25.module-true | u25-module-true.wast | 4 | 0 | 4/0/0; 0 | green control |
| U25.malformed-invalid | planted/u25-malformed-invalid.wast | 1 | 0 | 0/0/1; 0 | pending U28a |
| U25.outcome-protocol | u25-module-true.wast (trace required) | 4 | 0 | 4/0/0; 0, but 0 trace rows | RED |

`u25-malformed-invalid.wast` has valid binary grammar but an invalid function result type.
Wasm's syntax and validation judgments are distinct; an `assert_malformed` on those bytes is
false. Wasmtime's WAST harness accepts it. The suite therefore also requires independent
controls on the extracted binary: `wasm-tools print` rc 0 and `wasm-tools validate
--features=wasm2,-simd` rc 1. The FVA assertion must fail. A validator rejection cannot stand
in for a decoder rejection. The validating false assertion belongs to U25. Since U28a (Wasm
3.0's binary grammar restricted to P′), a binary that decodes fails the malformed assertion
(`assert_malformed: module decodes`), and the check is merged.

`U25.outcome-protocol` repeats the four-command matching-import case and requires a complete
trace. On `3ed6b36`, the aggregate is `4 0 0`, rc 0, but the trace is empty. Its checker prints
`outcome rows 0 != commands 4`, rc 1. That is a red-first check of the new public interface.

### D30 / U26 — machine properties

`make-memory` regenerates both WAST files. The small fixture compares all 1,024 seeded bytes
against a separate arithmetic memory mapping, including bytes outside the written interval.
Lengths = 0, 1, 31, 32, 33, 63, 64, 65, 255, 256, 257. It tests both overlap directions,
fill-byte truncation, passive-data offsets, source/destination bounds, zero-length endpoints,
address wrap, trap-before-write, memory growth and zero new bytes. The large copy checks every
one of 61,440 destination bytes and both outside boundary bytes.

| Check | Command | Baseline output | State |
| --- | --- | --- | --- |
| D30.memory-boundaries | R(d30-memory.wast) | `D30.memory-boundaries 63 0 0`; rc 0 | green control |
| D30.large-copy | R(d30-large-copy.wast) | no completed count row; timeout rc 124 after 180 s | RED / limit |
| D30.memory-copy | `FVA_SPEC_COUNTS=F scripts/test-spec memory_copy` | `memory_copy 97 0 4353`; rc 0; whole wall 4621 ms | RED |
| D30.wall | Same invocation, measured around the whole script | Not eligible: 4,353 commands skipped | RED |
| D30.full-mode | `FVA_SPEC_COUNTS=F scripts/test-spec` | `memory_copy 97 0 4353`; rc 0; whole wall 153985 ms | RED |

D30's <300 s acceptance requires nixbox, runner/corpus built, and no concurrent heavy job.
Desktop walls do not satisfy it. The suite prints the host and whole wall. It does not infer
an idle machine from a host name; the runner's owner must establish that condition. CI,
bootstrap, desktop, and replay costs remain separate measurements.

### D29 / U28 — P' behavior

| Check | File (`R(F)`) | Commands | Baseline p/f/s; rc | State |
| --- | --- | ---: | --- | --- |
| D29.handlers | d29-handlers.wast | 16 | 0/0/16; 0 | RED |
| D29.rethrow-tail | d29-rethrow-tail.wast | 5 | 0/0/5; 0 | RED |
| D29.typed-refs | d29-typed-refs.wast | 12 | 0/0/12; 0 | RED |
| D29.rec-imports | d29-rec-imports.wast | 8 | 1/0/7; 0 | RED |
| D29.assert-exception-return | planted/d29-exception-return.wast | 2 | 1/0/1; 0 | RED |
| D29.assert-exception-trap | planted/d29-exception-trap.wast | 2 | 1/0/1; 0 | RED |

Coverage = ordered duplicate/specific/all catch clauses; catch, catch_ref, catch_all,
catch_all_ref payloads; rethrow preserves the tag address and payload through two captures;
null throw_ref traps; traps stay traps; branch/return exits; callee-frame exceptions;
escaping exceptions; all three tail-call forms discard their local handler; typed calls and
null refinements; non-null table initialization; unset non-defaultable locals; canonical
rec-group identity, including a different projection and a different group shape at imports.
Wasm exposes no exnref equality instruction here; the rethrow test pins observable tag/payload
identity, not a hidden exception-allocation address.

| Check (`R(official/F.wast)`) | Commands | Allowed text skips | Required p/f/s | Baseline p/f/s; rc |
| --- | ---: | ---: | --- | --- |
| D29.official-tag | 10 | 0 | 10/0/0 | 0/0/10; 0 |
| D29.official-throw | 13 | 0 | 13/0/0 | 0/0/13; 0 |
| D29.official-throw_ref | 15 | 0 | 15/0/0 | 0/0/15; 0 |
| D29.official-try_table | 67 | 2 | 65/0/2 | 0/0/67; 0 |
| D29.official-return_call | 51 | 0 | 51/0/0 | 0/0/51; 0 |
| D29.official-return_call_indirect | 83 | 11 | 72/0/11 | 1/0/82; 0 |
| D29.official-return_call_ref | 53 | 0 | 53/0/0 | 0/0/53; 0 |
| D29.official-call_ref | 35 | 0 | 35/0/0 | 0/0/35; 0 |
| D29.official-br_on_null | 10 | 0 | 10/0/0 | 0/0/10; 0 |
| D29.official-br_on_non_null | 12 | 0 | 12/0/0 | 0/0/12; 0 |
| D29.official-ref_as_non_null | 7 | 0 | 7/0/0 | 0/0/7; 0 |
| D29.official-local_init | 10 | 0 | 10/0/0 | 0/0/10; 0 |

All 12 baseline official checks are RED. `D29.official-source-pins` runs
`(cd official && sha256sum --quiet -c SHA256SUMS)`, rc 0. Named text-format malformed exclusions:
`try_table.wast` lines 367, 372; `return_call_indirect.wast` lines 310, 322, 334, 346, 358,
370, 382, 389, 399, 409, 421. The exact diagnostics are also emitted to each recorded
`D29.official-*.exclusions` file. No binary, validation, runtime, GC-profile or type-soundness
obligation is excused by this exclusion.

### Per-command outcome contract / U25 + U28e

`FVA_SPEC_OUTCOMES=FILE` appends `line<TAB>type<TAB>outcome`, one row per JSON command.
The outcome is `pass`, `fail: line L: reason`, or `skip: line L: reason`.
`check-outcomes SCRIPT.json FILE` requires the exact command-key sequence, including repeated
keys and every command. For the dedicated 12 scripts, every non-text command must pass.
A text-format `assert_malformed` must report exactly `skip: line L: text format`, at its own
line. Any other skip, failure, missing/extra/reordered row or unrecognized class fails.

The selected dedicated scripts require zero `outside` skips. Thus legacy `outside wasm2,-simd`,
`outside P': construct`, decoder limitations, missing/rejected modules, unavailable imports,
and validation-only rejections cannot excuse one of their commands. Mixed 3.0 scripts may
legitimately need the named P' exclusions and dependent-command skips; U28e owns their exact
full-gate manifest and counts. This checker does not silently treat them as passes or claim
coverage of that future mixed-script manifest.

`D29.outcomes-validator` runs `test-outcomes`: 159 cases, including 32 fixed-seed generated
command lists with valid-trace, planted-failure, missing-row and changed-key properties.
Named cases cover EOF/empty inputs, repeated keys, row order/multiplicity, schema errors,
class prefixes and every forbidden skip family. Real checker → `159 cases; 0 failed`, rc 0;
a copy forced to `exit 0` → `159 cases; 123 failed`, battery rc 1. Seed = 439041101.
The official checks and the U25 protocol check read the runner's trace, not just aggregate counts.
The same battery checks ten status boundaries: raw process exits stay distinct from wrapped
script rc 2 (setup) / rc 3 (crash); timeouts, signals and unavailable commands propagate.
The old handler failed the wrapped-rc-3 canary; the corrected handler passes all ten without
changing the surrounding suite's flags.

### C++ / U28f, then U27+U29b

Source, exact build command, binary, runtime notices and provisional all-input goal =
`FVATest/Subjects/CppEH/`. Expected lift = `FVATest.Subjects.CppEH.Lifted`, namespace
`Subjects.CppEH.Lifted`; expected proof root = `FVATest.Subjects.CppEH.Proof`. The claim-form
part stays pending U27+U29b: the selected system claim uses `SysMust` under the declared WASI
profile E. The current import-free `Returns` draft is non-binding and must be replaced once
MAIN supplies the exact public system vocabulary. The stock SDK runtime remains unchanged.

| Check | Command / observable output on 3ed6b36 | State |
| --- | --- | --- |
| D29.cpp-build | `FVATest/Subjects/CppEH/build TMP/eh.wasm`; rc 0, `cmp` with shipped 44,913-byte artifact equal | green |
| D29.cpp-oracle | `wasmtime run -W exceptions=y,tail-call=y,function-references=y,gc=y --invoke eh eh.wasm X`; all eight calls rc 0 | green |
| D29.cpp-lift | `fva lift FVATest/Subjects/CppEH/eh.wasm TMP/Lifted.lean --ns Subjects.CppEH.Lifted` from the project root; rc 1 (`malformed value type`: no EH) | RED |
| D29.cpp-trust-default | `fva trust . --spec-module FVATest.Subjects.CppEH.Spec --root-module FVATest.Subjects.CppEH.Proof --subject FVATest.Subjects.CppEH.Lifted` | pending U27+U29b |
| D29.cpp-trust-paranoid | Same command + `--paranoid` | pending U27+U29b |

| Input bits (unsigned decimal) | Wasmtime signed i32 result |
| ---: | ---: |
| 0 | 1 |
| 1 | -1515870812 |
| 2 | 3 |
| 3 | -1515870810 |
| 2147483647 | -631612838 |
| 2147483648 | -2147483647 |
| 4294967294 | -1 |
| 4294967295 | 1515870810 |

The required claim quantifies over every `BitVec 32`; these eight calls do not replace it.
Its provisional syntax was checked against a contract-only empty-module stub with the public
claim attribute imported, rc 0. That check proves no property of `eh.wasm`.

**The import-free draft must be replaced, not proved.** `FVA/Spec/CAbi.lean:21` defines `Instance` with an empty
store and import list; `Instantiable` / `Returns` at lines 27 / 33 require an import-free
module. The real SDK artifact retains seven WASI imports. Thus its provisional `Returns`
goal cannot be proved. Even after linking imports, libunwind's throwing path reaches
`logAPIs → getenv → environ_sizes_get`; unrestricted host termination is not valid either.
The compiled export wrapper additionally calls `__wasm_call_dtors` / `__stdio_exit`.

`FVATest/Subjects/CppEH/probe-host-boundary` is a separate characterization probe, not one of
the 56 acceptance rows. It registers well-typed imports with a looping `environ_sizes_get`:
even input `0` returns `1`, rc 0; odd input `1` times out, rc 124 after three seconds. The
probe returns rc 0 when both observations hold. This establishes a reached host boundary;
it is not a gate that requires the dependency to remain. The ruling keeps the stock runtime
and selects an imported-module/system claim: `SysMust` under WASI E, with environment contents
stated in the claim. A profile without `LIBUNWIND_PRINT_APIS` can disable logging without
removing the real environment query. U28f keeps build/lift/EH evidence; the all-input statement
and proof follow U27 and the U29a/b model/host. Its exact Lean vocabulary stays pending; no
public API, environment default, replacement runtime or ABI stub was invented.

### WASI / D28 / U29

Build = `FVATest/Accept/LWR/wasi/build OUTDIR`, using `.tools/wasi-sdk`. The command is in that
script. `wasi/run-case wasmtime CASE OUTDIR CAPTURE` uses `wasmtime run`; the same helper with
`fva` uses the specified `fva run <wasm> [flags] -- [args]` interface. Stdin always comes from
a pipe. `wasi/expected/CASE/` holds exact stdout, stderr, exit and file layout; the `files`
case also holds every final file's exact bytes. Clocks and random bytes are called but never
printed. The suite compares bytes with `cmp`, not whitespace-normalized text.

| Check | Inputs / output | Baseline |
| --- | --- | --- |
| D28.declared-imports | `wasi/check-imports OUTDIR` → `declared WASI imports: 20`, rc 0 | green |
| D28.oracle-process-empty | No args/env; empty pipe → `argc=0`, `envc=0`, empty stdin, stderr marker, exit 0 | green |
| D28.oracle-process-values | Two `--env` flags; five args (plain, spaces, empty, option-like, UTF-8); `pipe-input` → exact recorded bytes, exit 0 | green |
| D28.oracle-files | `--dir CAPTURE/tree::/sandbox`, seed file → exact stdout/stderr and final two files, exit 0 | green |
| D28.oracle-exit7 | Before-exit stdout + stderr; proc_exit → exit 7 | green |
| D28.run-process-empty | Same process-empty inputs through `fva run` | pending U29b |
| D28.run-process-values | Same process-values inputs through `fva run` | pending U29b |
| D28.run-files | Same files inputs through `fva run` | pending U29b |
| D28.run-exit7 | Same exit7 inputs through `fva run` | pending U29b |
| D28.bustools | SysMust + exact 168-byte B + normalized golden corollary, every random value, default/paranoid trust | pending U29f public subject seam |

`wasi/imports` lists all 20 declared calls. The file scenario covers preopen bytes, regular
file/directory types, CREAT/TRUNC/EXCL, missing/existing-path errors, short chunked reads,
SET/CUR/END seeks (including after EOF), append flags, sparse extension and zero bytes,
independent per-open offsets, an unlinked but still open file, mkdir/nonempty rmdir/unlink/rmdir,
fdstat flags, close and double-close. Process scenarios check args/environ data and exact
byte-size sums, including terminators and UTF-8. They also cover clock kinds, zero/nonzero-length
random calls, stdin and both output streams.

### D51 / U30–U31

`D51.java-all-input` = pending: the route pick must fix the public unchanged-function subject,
all-input claim and trust command. `D51.gc-conformance` = pending: the selected route must fix
the official WasmGC conformance selector. This suite invents neither API.

## Whole-suite baseline and final committed run

Historical whole runs at `e4ba19c92be26ea95b97f4fc341f03c2d4ca97d7` and
`5302be991cb4c728fe0a9b9a9b53dfbf0015be46` returned rc 3: 54 checks, 14 ok / 31 FAIL / 9 pending.
The latter replay matched every committed status. Its desktop walls were 3.948 s for named
memory_copy and 164.635 s for full mode; both still skipped 4,353 commands. These are not D30
success or nixbox measurements. The rulings add two outcome checks and move one malformed-stage
case from FAIL to pending U28a; the original fixture bytes and required behavior are unchanged.

Current committed-run command = `scripts/test-accept-lwr --record .scratch/lwr/final-commit`,
under `offload run --local -- nice -n 10`. FVA implementation stays `3ed6b36`, unread.
Raw final output = `.scratch/lwr/final-commit-suite.log`; commands/output/rc/walls/traces =
`.scratch/lwr/final-commit/`. These are local evidence, not required suite inputs.
The suite returns rc 3 because `D30.large-copy` reaches its 180 s execution limit.

| Group | Checks | ok | FAIL | pending |
| --- | ---: | ---: | ---: | ---: |
| U25 | 14 | 5 | 8 | 1 |
| D30 | 5 | 1 | 4 | 0 |
| D29 P' | 20 | 2 | 18 | 0 |
| D29 C++ | 5 | 2 | 1 | 2 |
| D28 | 10 | 5 | 0 | 5 |
| D51 | 2 | 0 | 0 | 2 |
| Total | 56 | 15 | 31 | 10 |

Current status output follows. Reasons and raw baseline counts are in the tables above;
wall lines are excluded because they vary by run. The final committed run is compared with
this complete status block.

<!-- final-status-begin -->
```text
FAIL U25.function-false
ok U25.function-true
FAIL U25.global-false
ok U25.global-true
FAIL U25.memory-false
ok U25.memory-true
FAIL U25.table-false
ok U25.table-true
FAIL U25.malformed-false
FAIL U25.malformed-true
FAIL U25.module-false
ok U25.module-true
pending U25.malformed-invalid
FAIL U25.outcome-protocol
ok D30.memory-boundaries
FAIL D30.large-copy
FAIL D30.memory-copy
FAIL D30.wall
FAIL D30.full-mode
ok D29.outcomes-validator
FAIL D29.handlers
FAIL D29.rethrow-tail
FAIL D29.typed-refs
FAIL D29.rec-imports
FAIL D29.assert-exception-return
FAIL D29.assert-exception-trap
ok D29.official-source-pins
FAIL D29.official-tag
FAIL D29.official-throw
FAIL D29.official-throw_ref
FAIL D29.official-try_table
FAIL D29.official-return_call
FAIL D29.official-return_call_indirect
FAIL D29.official-return_call_ref
FAIL D29.official-call_ref
FAIL D29.official-br_on_null
FAIL D29.official-br_on_non_null
FAIL D29.official-ref_as_non_null
FAIL D29.official-local_init
ok D29.cpp-build
ok D29.cpp-oracle
FAIL D29.cpp-lift
pending D29.cpp-trust-default
pending D29.cpp-trust-paranoid
ok D28.declared-imports
ok D28.oracle-process-empty
pending D28.run-process-empty
ok D28.oracle-process-values
pending D28.run-process-values
ok D28.oracle-files
pending D28.run-files
ok D28.oracle-exit7
pending D28.run-exit7
pending D28.bustools
pending D51.java-all-input
pending D51.gc-conformance
test-accept-lwr: 56 checks; 15 ok; 31 FAIL; 10 pending
```
<!-- final-status-end -->

Additional checks: separate `bash -n` invocations, shellcheck and shfmt pass for all nine Bash
files; the two generated memory fixtures replay byte-identically; the C++ draft syntax checks
on a contract-only stub, not on the real artifact. The outcome-validator battery passes all
159 cases and fails on the forced-green checker with 123 failed cases, rc 1.
Planted extra WASI import → check-imports rc 1; planted changed official source byte → sha256
check rc 1. `git diff --check` reports three intentional blank EOF records: two byte-preserved
upstream licenses and exact pipe stdout. All other paths pass that whitespace check.

## Limits

- Formal soundness, simulation, environment nonemptiness/inclusion, and all-input claims need
  kernel-checked theorems, not finite execution tests. This suite does not certify those proofs.
- C++ SysMust vocabulary (U27+U29b), D28 seed framing/golden proof, and D51 route-specific
  proof/conformance stay pending their public seams. These rows count and keep the suite non-green.
- The full mixed 3.0 script manifest and named outside/dependency accounting belong to U28e;
  this suite independently pins the dedicated 12, not a guessed future mixed manifest.
- Baseline-green controls/oracles were not mutation-qualified. Mutation and the product's full
  `scripts/gate` were not run by this blind author. The acceptance suite intentionally remains red.
- Shared `.lake/packages`, `.tools` and `.cache/corpus` are read-only inputs; private builds and
  all generated fixtures/captures stay in this worktree. No FVA, gate, rule or state file changed.
