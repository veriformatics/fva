# WASI CLI IO corpus

Source = `docs/contracts/U29b-host.md`, U29b2 + CLI facts; model/departures =
`docs/contracts/U29a-wasi.md`. FVA implementation unread when authoring.

## Run

```sh
FVATest/Wasi/run/make --check
FVATest/Wasi/run/check wasmtime
FVA=/absolute/path/to/fva FVATest/Wasi/run/check fva
FVATest/Wasi/run/self-test
```

`--case ID` selects one row. `WASMTIME` + `WASM_TOOLS` override tool paths; oracle
version must stay 50.0.0, parsed module hashes must match `wasm.sha256`.
`FVA_RUN_OUT` selects an output parent (default `.cache/wasi-run`);
`FVA_RUN_KEEP=1` retains successful bundles. Failed bundles always stay.
`FVA_RUN_RECORD=PATH` saves the successful run's capture-hash table.

116 cases = 63 exact-wasmtime + 2 relational + 51 named departures. `check wasmtime`
grades the first 65; it prints each departure as FVA-only. `check fva` grades all 116.
A declaration is not a skipped failure: each basis precedes FVA grading, and a
failure keeps its classification. No FVA implementation pass is claimed here.

## Inputs + captures

- `cases.jq` → `make` → `cases.json`, `case-ids.json`, `cases.tsv`.
- `common.wat` + `programs/NAME.wat` → `(module …)` → wasm-tools parse.
  `standalone/*.wat` bypasses common imports to exercise load boundaries.
  `load-undecodable.wasm` = a fixed non-module byte string. No compiler/sysroot.
- Case = `id`, coverage `rows`, `program`, `basis`, `opts`, `args`, `stdin`, input
  `tree`, expected `stdout`/guest `stderr`/`rc`/`tree`; optional fault/observer mode.
- Bytes = `{text: UTF8}` or `{hex: lowercaseHex}`. Tree rows = relative `path` +
  `kind` (`d`, `f`, `l`, `h`, `p`); file `bytes`; link `target`. Non-regular rows
  exercise pre-run rejection alone. Explicit empty directories/files survive Git
  through the table. Names include spaces, Unicode and embedded/trailing newlines.
- Every run gets fresh input + expected trees. Binary stream/file equality = `cmp`;
  layout = every relative path + kind, NUL-delimited + byte-sorted; symlink targets
  checked too. Root/unchanged-entry identities stay (device + inode check): a
  delete-all/recreate sync is not accepted even with byte-identical output.
- `process.wasm` emits `ARGS\0`, NUL-terminated args, `ENV\0`, NUL-terminated env,
  `STDIN\0`, stdin. Thus empty/duplicate/option-like values remain observable.
  FVA receives separate option/value arguments; wasmtime receives `--env=VALUE`
  to keep option-like env values out of clap's option parser. Guest inputs match.
- `oracle.tsv` = recorded successful captures (rc + stdout/guest-stderr/layout/file
  digest). RNG payload hashes are observations, never fixed random expectations.
  Expected exact captures are the byte fields + trees in `cases.json`.
- Failure bundle = quoted command, stdin, initial hashes, stdout, raw + guest stderr,
  diagnostic suffix, exit status, layouts, file digests, byte/layout diffs.

## Coverage + limits

- Parser property seed 271828, 24 generated argument/env vectors; tree seed 314159,
  24 generated import/export/in-place-sync round trips, half with mutations.
  Domains = UTF-8 strings without NUL, supported tree shapes, finite stdin; these
  finite fixed-seed samples are evidence, not exhaustive proofs.
- First-chunk observer reads `FIRST\n` while a guest loops without terminating,
  then terminates the observer-owned process. Its signal status is not a guest
  ending assertion. Merged-stream replay pins write order; separate replay pins
  exact stdout/stderr bytes and once-only suffix emission.
- Default RNG: 64 output bytes; two 32-byte calls must differ (false-positive
  probability 2^-256 under independent uniform bytes). Fixed HEX tests pin reuse,
  truncation, zero-padding and case-insensitive decoding. No RNG-failure injection.
- Faults = unreadable file, directory as stdin, unwritable sync root, `/dev/full`
  for stdout/stderr. Permission probes require a non-root runner; the harness
  confirms the denied permission before the run. Stderr-failure diagnostics cannot
  be captured from the failed stream; that row grades rc + stdout + file effects.
- Departures cover frozen clocks, fixed random bytes, large exit codes, diagnostics,
  out-of-profile/NaN/fuel stops, load/option/filesystem-shape rejection and host IO
  failure. No fixture fabricates a valid well-typed stuck Wasm execution; positive
  runs fail if the driver misclassifies one as stuck. Natural OS exhaustion and
  hostile concurrent filesystem mutation are outside these finite probes.
- The harness's 30 s observer timeout is infrastructure protection, not FVA fuel.
  The live-chunk observer uses 5 s for the first chunk and a 10 s process guard.
- Diagnostic framing = contract `d453b50`: at most one FVA diagnostic follows the
  final guest byte, without an inserted newline; `split-stderr` separates at the
  last `fva run: ` occurrence. `diagnostic-marker` pins unterminated binary guest
  stderr containing two earlier markers. Cases check the diagnostic prefix; large
  exits also require their numeric code, capture/sync faults their specified path.
  Message wording stays ungraded. Marker-only guest output without an
  actual FVA diagnostic remains outside these finite probes.

`self-test` grades 12 controls: binary last-marker/no-marker framing, a 16-input
framing property (seed 161803; byte lengths 0–256, 0–3 guest markers) + a normal
oracle row pass; altered stream/file bytes, wrong rc and missing tree entry fail
rc 1; missing/duplicate/unclassified case or missing program fail rc 2. Replacing
`check` by success-only code makes it fail. First-marker framing fails the binary
fixture (4 guest bytes instead of 41).
