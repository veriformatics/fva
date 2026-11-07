# Behavior characterization

Baseline = `dceb87eb1971170decdd6bb0ba4a1cdbf9a04578` (the runner outcome hook).
Goldens regenerated at the U25 + U26 landing (import matching, binary malformed, the machine
runner executing `memory_copy`); that commit body holds the reviewed golden diff.
Goldens describe observed behavior, not a correctness oracle.
An intended change requires an explicit, reviewed golden diff.
Suite = Bash + text fixtures/goldens; no new Lean module, Lake target or cache.
Implementation bodies stay unread.

| Surface | Pinned items | Verification |
| --- | --- | --- |
| Full official scripts | 82 scripts; 27,373 command rows | PASS, rc 0; all command tallies agree with runner summaries |
| Fast official scripts | 80 scripts; 27,156 command rows; excludes only bulk + memory_fill | PASS, rc 0 |
| CLI help | 12 invocations; stdout + stderr + exit status | Byte-exact; `help --help` returns 2, the other 11 return 0 |
| Tracked Wasm lifts | 20 files; namespace `CharLift` | 19 return 0 with a SHA-256-pinned module; `FVATest/Subjects/CppEH/eh.wasm` (exception handling: outside the profile until U28) returns 1 |
| Comparator + trace-join controls | 16 cases, including skip reason classes and a direct same-line runner fixture | PASS |
| Full / fast wall time | Full comparison 61 s; fast comparison 52 s | Every selected script, help call and lift executes afresh |

## Run

```sh
scripts/test-char --fast
scripts/test-char
scripts/test-char --regen
scripts/test-char-fixture
```

Prerequisites: pinned Lean toolchain, Mathlib cache, `.tools/bin/wasm-tools`,
`jq`, Git and GNU coreutils. Fetch the corpus with `scripts/fetch-corpus`.
The suite builds the existing `fvatest` + `fva` targets under `nice`.
Script workers = four; `FVA_CHAR_JOBS=N` changes the count.
Corpus, tools and package symlinks remain read-only.
Temporary captures stay inside this checkout and are removed at exit.

Exit status: 0 = equal; 1 = mismatch; 2 = setup; 3 = crash or timeout.
Help/lift/validator calls have a 60 s timeout; a script has a 900 s timeout.
The comparison prints each changed file and its full diff.
`--regen` re-observes the full corpus and rewrites only capture files.
`--fast --regen` is rejected: regeneration must cover all goldens.
Every selected script, help call and lift executes on every run.

## Captures

- `outcomes/<script>.tsv`: source line, command type, outcome, binary-validation
  verdict. Every selected official command has one row, in execution order.
  Outcome = `pass`, `fail`, or `skip:<reason class>`.
- `scripts.tsv`: script, execution mode, pass/fail/skip, then the runner's
  validation counters (module, unlinkable, uninstantiable, invalid, malformed,
  outside, undecodable).
- `help/`: `lake exe fva help` and each advertised command's `--help`; separate
  stdout, stderr and exit status. `commands.txt` pins the command inventory.
- `lift.tsv`: path, exit status, generated-module SHA-256 for every
  `git ls-files '*.wasm'` entry, through `lake exe fva lift`.
  Input paths are repository-relative; namespace = `CharLift`.
- `observer.wast` / `observer.tsv`: a function returning 7; one true return
  assertion, one false return assertion and one false trap assertion.
  Two assertions share a source line. Runner totals must be 2/2/0, rc 1.

## Direct observation

For each selected script, run `wasm-tools json-from-wast` exactly as
`scripts/test-spec` does, then execute:

```sh
FVA_SPEC_OUTCOMES=<trace> .lake/build/bin/fvatest spec <script.json>
```

The runner itself writes `line<TAB>type<TAB>outcome` from the same tally entry
that produces its summary. The suite neither dispatches commands nor infers
passes from missing diagnostics. `normalize-outcomes` checks trace identity,
order and completeness against JSON metadata, including repeated source lines.
It preserves pass/fail and the skip reason class. The tally diagnostic line
prefix, profile/decoder offsets and multiline diagnostic continuations do not
enter the class; malformed skips retain the binary/text distinction.

Binary module candidates (`module`, `assert_invalid`, `assert_unlinkable`,
`assert_uninstantiable`) also run through the existing `fvatest validate`
batch interface. Their per-command verdict = `valid`, `invalid`, `malformed`
or `unsupported`; candidate count/order is checked. Text candidates are named
`not-run:text` in this independent binary-validation column. Malformed-command
validation is `not-run:malformed`; non-payload commands use `-`.
The runner's own validation behavior remains pinned by its direct outcome
and its aggregate counters, including any text parsing it performs.

`memory_copy` executes in both modes: 4,450 passes. Full mode omits no script.
Fast mode omits only `bulk` + `memory_fill`, exactly as `scripts/test-spec --fast`
does. Their full goldens remain committed.

## Evidence

| Command / check | Output / result |
| --- | --- |
| `nice -n 10 lake --wfail build fvatest fva` | rc 0 |
| `scripts/test-char --regen` (U25 + U26) | rc 0; 82 scripts, 27,373 commands, 12 help calls, 19 lifts; 51 s |
| `scripts/test-char --fast` (U25 + U26) | rc 0; 80 scripts, 27,156 commands, 12 help calls, 19 lifts; 52 s |
| `scripts/test-char` before the U25 + U26 regeneration | rc 1; 31 changed captures, each an expected class; 61 s |
| `scripts/test-char-fixture` | rc 0; `16 passed, 0 failed` |
| Skip-class regression on `2ede585` | Fixture battery rc 1; `15 passed, 1 failed`; fixed by stripping the tally diagnostic line prefix |
| Forced-exit-0 comparator | Fixture battery rc 1; `9 passed, 7 failed` |
| Forced-exit-0 trace join | Fixture battery rc 1; `8 passed, 8 failed` |
| Capture structure + trace tallies | 27,373 four-column rows; all 82 normalized tallies equal direct runner summaries |
| Hook/Lake footprint | No Lean-module or Lake-file diff against `dceb87e` |
| shellcheck + shfmt + Bash syntax + diff checks | rc 0 |

Walls = observed elapsed times under `nice`, not isolated performance benchmarks.
Coverage = the committed corpus, not a proof of Wasm semantics.
The full project gate and implementation mutation campaign are not run by
this task. Fixture plants prove harness detection; they do not claim mutation
credit for the implementation.
