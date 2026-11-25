# U28f contract — the C++ throw/catch subject: SDK pin, fingerprint, lift, EH run on the machine (tier: data)

Purpose: `FVATest/Subjects/CppEH` (`eh.cpp` → `eh.wasm`, 44,913 B, sha256 `4e2fe131…5292`;
Decisions: C++ example) becomes a subject rebuilt from committed state, its EH form + import
boundary checked, lifted, and its throw → catch run on the verified machine with the source's
results — so U28g proves the all-input system claim on these exact bytes. Consumers: U28g (claim
over `Lifted.module`, the run's host binding as its starting harness), U29b (its executable WASI
host replaces the stub), acceptance `D29.cpp-build` + `D29.cpp-oracle` (merged here).

Tier `data`: U28g re-validates the bytes (`decode_eq` by the kernel, `fva trust`'s link check) and
every behavior by proof; the run here = evidence that FVA's EH semantics (machine = reference
stepper = `Step`) matches the source contract on compiled libc++abi/libunwind code, which no
official script reaches.

Review: no consultant (tier `data`; the probe below settled the execution route; the open
questions resolved by evidence: the SDK fetch is already committed, the mutation keying rules out
an `fvatest` command); advisor on this contract; MAIN-led review + one `reviewer` on the unit's
diff before landing.

## Facts at the pin (`370c959`, before U28f)

Pre-unit state; where it differs, Interface + Results state the current behavior.

- SDK: `scripts/fetch-bench-tools wasi-sdk` = wasi-sdk 34.0 release tarball (192,383,077 B,
  sha256 `b761e3a0…b2c4`) → `.tools/wasi-sdk` + stamp `.pin-34.0`; `VERSION` = `34.0`,
  `wasi-libc: 2e6fb9d8ee0c`, `llvm: 895aa2c896ad`, `llvm-version: 23.1.0`,
  `config: f992bcc08219`. `build` takes whatever SDK sits at `.tools/wasi-sdk` or
  `WASI_SDK_PATH` (no version check) and nothing fetches it on a gate host. The SDK's
  `libLLVM` → bundled `libedit` → `libtinfo.so.6`, which the SDK does not bundle: Arch + Ubuntu
  ship it; nixbox's nix-ld set lacks it (listed: `libstdc++`, `libgcc_s`, no `libtinfo`;
  nixpkgs `ncurses` 6.6 provides `libtinfo.so.6`).
- `wasm-tools print eh.wasm` (17,003 lines): imports = 7 `wasi_snapshot_preview1` functions
  (`environ_get`, `environ_sizes_get`, `clock_time_get`, `fd_close`, `fd_seek`, `fd_write`,
  `proc_exit`); exports = `memory`, `eh` (`$eh.command_export`: wasm-ld's wrapper, ctors + `eh`
  + dtors per call); 14 `try_table` (clauses: 1 `catch`, 1 `catch_ref`, 11 `catch_all`, 1
  `catch_all_ref`), 1 `throw`, 2 `throw_ref`; no legacy `try`/`catch`/`catch_all`/`delegate`/
  `rethrow` instruction; names kept (`--strip-debug` keeps the name section).
- Odd path = `__cxa_throw` → `_Unwind_RaiseException` → `logAPIs` → `getenv` →
  `environ_sizes_get` (+ `environ_get` when the count ≠ 0; libunwind + wasi-libc cache both per
  process) → `throw` → caught in `eh`; even path calls no import (tester-1's
  `probe-host-boundary`).
- Probe (`.scratch/lwr/u28f/probe/Probe.lean`, `lake env lean --run`, interpreted, U28e tree):
  decode + `Machine.instantiate` (83 ms) with one host function per import, then
  `Machine.sysRun` per input from the instantiated store with a stub answering
  `environ_sizes_get` = 0/0: x = 0 → 1, 2 → 3 (0 host calls, 0 exception instances, 3–9 ms);
  x = 1 → `0xa5a5a5a4`, 3 → `0xa5a5a5a6` (1 host call, 1 exception instance, 57–101 ms) = the
  source contract.
- Mutation keys (`FVATest/Mutate/config.json`): `FVATest/Main.lean` is an input of 5 stages
  (decoder, numerics, floatdiff, spec, p2exec) → a new `fvatest` command re-keys ≈ 1,050 killed
  rows + 83 survivors (≈ 12 h of pool `--update`); `FVATest/Subjects` is outside the module graph
  and no stage reads it, nor `scripts/test-subjects`, `scripts/test-checks`, `scripts/check-notices`
  or `bench/subjects/manifest.json`.
- Acceptance: `D29.cpp-build` + `D29.cpp-oracle` green at bd00b00 (no FVA code involved) =
  controls; `D29.cpp-lift` merged at U28a; `Spec.lean` = tester-1's non-binding `Returns` draft
  (false for this artifact) → rewritten by U28g, built by nothing until then.

## Interface

- I1 SDK pin enforced: `build` uses `WASI_SDK_PATH` when set, else `.tools/wasi-sdk`, fetched by
  `scripts/fetch-bench-tools wasi-sdk` when its `.pin-34.0` stamp is absent; an SDK whose
  `VERSION` differs from the five pinned lines → rc 2 naming the SDK, nothing built. nixbox:
  `ncurses` joins `programs.nix-ld.libraries` (`~/Projects/offload/machines/nixbox`, deployed
  while nixbox runs no job).
- I2 Fingerprint `FVATest/Subjects/CppEH/fingerprint WASM` (over `wasm-tools print`,
  independent of FVA's decoder): rc 0 iff every import is a `wasi_snapshot_preview1` function
  among the Decisions' 20 declared preview1 calls, the exports are exactly `memory` + `eh`, at
  least one `try_table` and one `throw` occur, and no legacy EH instruction (`try`, `catch`,
  `catch_all`, `delegate`, `rethrow` as a line's instruction, apart from `try_table`'s
  parenthesized clauses) occurs; prints `imports N try_table N throw N throw_ref N` + the clause
  counts; rc 1 a violation (each named), 2 setup. `build` runs it on its output (its rc decides)
  → `D29.cpp-build` checks it in the full gate. The 20 names = the Decisions' list until U29a's
  reviewed model owns it (U29a points the check at the model's list).
- I3 Lift committed: `FVATest/Subjects/CppEH/Lifted.lean` = `fva lift
  FVATest/Subjects/CppEH/eh.wasm … --ns Subjects.CppEH.Lifted`; `scripts/test-subjects`
  regenerates it and fails on any byte difference (as for GlmCall's `fva call` output);
  `decode_eq` kernel-checked in the subject build; `bench/subjects/manifest.json` `builds` entry
  `cpp-eh-wasm` (sha256, licenses, upstream, version, corresponding source) + the existing NOTICE
  → `scripts/check-notices` covers the literal.
- I4 EH run on the machine `FVATest/Subjects/CppEH/Run.lean` (test-only; imports the machine,
  decoder + `Lifted`, never a proof module): decodes `Lifted.bytes` (`decode_eq` ties it to
  `Lifted.module`), binds host function i to import i (type = the module's defined type; checked
  by `Ref.importsMatch`), instantiates once on `Machine.instantiate`, then runs `eh` on every
  input from the instantiated store (= a fresh process per call, as `wasmtime run --invoke`)
  through `Machine.sysRun` with a fail-closed stub: `environ_sizes_get(count, size)` writes u32 0
  at both pointers of the instance's exported `memory` and returns `[i32 0]` (= wasmtime's default
  empty environment); a pointer past the memory or any other import → no outcome, the run stops.
  Inputs = the acceptance oracle's 8 (0, 1, 2, 3, 2^31−1, 2^31, 2^32−2, 2^32−1) + 64 from a
  fixed-seed generator. Each input: fuel left, ending `.returned [i32 r]`, r = x + 1 (even) or
  x ^ 0xa5a5a5a5 (odd) mod 2^32; odd → 1 exception instance + 1 host call, even → 0 + 0. A
  build-time `#eval` throws `CppEH run: …` listing every failing input; test-subjects builds
  `Run` apart from the proof roots: a failed build whose log carries `CppEH run:` → rc 1, any
  other build failure → rc 2. `Run`'s import closure holds no `FVA/Proof/**` module (a planted
  machine bug then reaches the run, never a proof first).
- I5 Acceptance: `D29.cpp-build` + `D29.cpp-oracle` appended to `FVATest/Accept/LWR/merged`.
- I6 Rules + docs: `fva-checks.md` entries (test-subjects `Run` + its plants, test-checks'
  fingerprint cases, check-notices' new artifact, test-accept's two IDs); the subject README
  (SDK fetch + pin, fingerprint, `Run`, the stub's scope); Tasks acceptance counts.
- Out: the claim + proofs (U28g), the WASI model (U29a), the executable host + `fva run` (U29b;
  `Run`'s stub retires there), `Spec.lean`'s rewrite (U28g).

## Evidence

- E1 Fresh SDK: a scratch clone with an empty `.tools` → `build` fetches the pinned SDK and emits
  bytes `cmp`-equal to `eh.wasm`; the same on nixbox after the nix-ld deploy (`offload run --host
  nixbox`), wall recorded.
- E2 Plants (scratch copies, restored + `cmp`; the shared `.tools/wasi-sdk` never edited —
  `WASI_SDK_PATH` at a reflink copy): build — `VERSION` edited → rc 2, the legacy-EH
  flag (`-wasm-use-legacy-eh=true`) → fingerprint rc 1 → build rc 1; fingerprint (test-checks,
  `wasm-tools parse` of edited print text) — an import outside the 20 (`sock_accept`), a legacy
  `try … end`, the `throw` removed, an extra export → rc 1 each, clean → rc 0, the check
  neutered (`exit 0`) → test-checks red; acceptance — one flipped byte in `eh.wasm` →
  `D29.cpp-build` FAIL, `eh.wasm` rebuilt from an `eh.cpp` whose catch XORs `0xa5a5a5a4` →
  `D29.cpp-oracle` FAIL.
- E3 `Run`: 72/72 inputs as I4; wall of the `Run` build and of `Lifted`'s `decode_eq` (wall + RSS
  under the 16 GiB cap).
- E4 `Run` plants (each patched, `Run` rebuilt — Lake's log shows `Run` re-elaborated —,
  restored + `cmp`): the machine's handler search
  skipping `catch_all` clauses; a `catch` clause pushing no payload; `throw_ref` trapping;
  `hostResume` dropping the host's results; the stub reporting one environment variable (the
  fail-closed stop at `environ_get`) → `Run` red each.
- E5 `check-notices` over the new literal: the NOTICE without its sha256 line → rc 1.
- E6 test-subjects' regeneration check: `Lifted.lean` with one changed literal digit → rc 1 naming
  the file.
- E7 Measurement (Results only, for U28g's method choice): one odd input's `sysRun` equality by
  `decide +kernel` (wall + RSS), or the limit it hits.
- E8 Mutation: no stale row (`scripts/test-mutation check` rc 0 on the U28f tree after U28e's
  update lands).

## Results

- E1: an empty `.tools` (scratch tree: `scripts/fetch-bench-tools` + the subject's `build`,
  `eh.cpp`, `fingerprint`) → `build` fetched the pinned SDK (192,383,077 B, sha256-checked),
  built, fingerprinted and emitted bytes `cmp`-identical to `eh.wasm` in 12 s; with the SDK present
  `build` takes 0.4 s (`.scratch/lwr/u28f/e1/local.log`, load ≈ 23 on 8 CPUs). An output under
  another basename differs in the name section (wasm-ld records the basename; `e1/local-basename-probe.log`). nixbox, after the nix-ld `ncurses` deploy (offload `c89b4e8`): `build` with the
  SDK present → rc 0 in < 1 s, the fingerprint's counts as shipped, bytes `cmp`-identical to
  `eh.wasm` (`e1/nixbox.log`).
- E2 (scratch copies; the shared SDK untouched): `VERSION` with another `llvm:` line → rc 2,
  nothing built; `VERSION` absent → rc 2; `-wasm-use-legacy-eh=true` → fingerprint rc 1 (legacy
  `try`, `catch`, `rethrow` at lines 53, 59, 89; the SDK runtime keeps 13 `try_table`). test-checks'
  fingerprint battery: 5 planted print texts → rc 1 each, each for its own reason (`sock_accept`
  outside the declared calls, `env f`, legacy `try`, `no throw`, `unexpected export extra`); the
  shipped file → rc 0; the check neutered (`exit 0`) → 5 cases red. Acceptance (`test-accept-lwr
  --group CppEH`): clean → `ok` build, oracle, lift (trust pending U28g); the last byte of `eh.wasm`
  flipped → `FAIL D29.cpp-build` alone; `eh.wasm` built from a catch XORing `0xa5a5a5a4` →
  `FAIL D29.cpp-build` + `FAIL D29.cpp-oracle`; restored, `cmp` ok.
- E3: `Run` = 72/72 inputs on the contract (36 odd: 1 host call + 1 exception instance each;
  36 even: none); `lake env lean` under a 16 GiB cap, two samples (`.scratch/lwr/u28f/e3/`, load
  ≈ 21–23 on 8 CPUs): `Run` 8.8–10.2 s, 2.6 GB peak RSS; `Lifted` (`decode_eq`) 50–51 s, 3.5 GB. A wrong even expectation → `CppEH run:
  36 of 72 inputs off the contract`, build rc 1 (the `#eval` runs).
- E4 (`.scratch/lwr/u28f/e4/`, each patched, `Run` rebuilt, restored, `cmp` ok; final build rc 0):

  | plant | file | result |
  |---|---|---|
  | `throw_ref` traps | Machine | 36/72 off: odd inputs stop after their host call |
  | `hostResume` drops the host's results | Machine | 36/72 off: odd inputs stop |
  | a `catch_ref` clause pushes no payload | Ref | 36/72 off |
  | tagged clauses never match | Ref | 36/72 off: `uncaught exception 0` |
  | the stub reports one environment variable | Run | 36/72 off: stop at `environ_get` |
  | `catch_all` clauses skipped | Ref | no change |
  | a `catch` clause pushes no payload | Ref | no change |

  The last two are off the run's path: `eh` catches through `catch_ref` (`__cpp_exception`), and no
  `catch_all` clause changes an observation of these 72 runs; the contract's E4 named the first,
  so `catch_ref` + tagged-clause plants replace both as the run's firing evidence.
- E5: check-notices on the tree → rc 0; a copy whose NOTICE lacks the sha256 line → rc 1 naming
  `FVATest/Subjects/CppEH/Lifted.lean`.
- E6: the regeneration block of test-subjects (run alone) → clean `fail=0`; `Lifted.lean` with one
  literal digit changed → `is not fva lift's output (regenerate it)`, `fail=1`; restored, `cmp`.
- E7 (`.scratch/lwr/u28f/e7/`): `okFor Lifted.module 1 = true` by `decide +kernel` — instantiation
  + the whole odd-path `sysRun` (stub host, throw → `catch_ref` → return `0xa5a5a5a4`) on
  `Lifted.module`, no decode — accepted in 34 s wall, 4.3 GB peak RSS (file total: imports +
  elaboration + kernel; 12 GiB cap, loaded desktop); control `okFor Lifted.module 1 = false` → kernel
  `application type mismatch` (rc 1). A concrete input's whole run is cheap for the kernel; U28g's
  all-input claim still needs a symbolic method for the payload (U28d: a symbolic `i32` stalls at
  `Ref.toVal`).
