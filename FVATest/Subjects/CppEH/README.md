# C++ exception-handling subject

Contract = D29 / U28f in `.agent/spec.md`, Language + Wasm reach.
`eh.cpp` defines one function over every `uint32_t` input. Even inputs return their successor
modulo 2^32. Odd inputs throw that value and catch it in the same function. The catch returns
its bitwise XOR with `0xa5a5a5a5`. Unsigned arithmetic has no signed-overflow case.

## Build

`eh.wasm` is not committed: it links third-party runtime code (Decisions: Repository contents).
`scripts/fetch-subjects` places the pinned build (sha256 `4e2fe131…`, release `subject-builds-v1` of
veriformatics/fva-artifacts, with its notice `NOTICE-eh.txt` and the runtime licenses
`license-*.txt`).

Run `FVATest/Subjects/CppEH/build [OUT.wasm]` to rebuild it. Without an output path, the script
writes `eh.wasm` here. The script uses the SDK at `.tools/wasi-sdk`. If that SDK is missing, the
script gets the pinned wasi-sdk 34.0 release with `scripts/fetch-bench-tools wasi-sdk`, which
checks the sha256 of the release tarball. Set `WASI_SDK_PATH` only when the SDK is at another
path. The script refuses an SDK whose `VERSION` file differs from the pinned release (rc 2). After
the compile, the script runs `fingerprint` on its output, and the fingerprint decides the result.
The full gate rebuilds the subject and compares the bytes with the pinned build (acceptance check
`D29.cpp-build`). The SDK's clang loads `libtinfo.so.6` from the host system.

Exact compiler command (`SDK=.tools/wasi-sdk`):

```sh
"$SDK/bin/clang++" --target=wasm32-wasip1 -std=c++17 -O1 \
  -fwasm-exceptions -mllvm -wasm-use-legacy-eh=false \
  -nostartfiles -Wl,--no-entry -Wl,--export=eh -Wl,--strip-debug \
  -Wl,-z,stack-size=65536 -Wl,--initial-memory=262144 -Wl,--max-memory=262144 \
  FVATest/Subjects/CppEH/eh.cpp -lunwind -o FVATest/Subjects/CppEH/eh.wasm
```

The SDK links its real libc++abi and libunwind. The source supplies no exception-runtime
functions. This is a no-entry library, not a WASI command. Memory is fixed at 256 KiB. The
oracle's fresh throwing calls succeed at this limit. The linked runtime retains seven WASI
imports: `environ_get`, `environ_sizes_get`, `clock_time_get`, `fd_close`, `fd_seek`, `fd_write`,
`proc_exit`. The system claim states their allowed environment profile and binds the host to
the instance's exported memory. Removing these imports or replacing them with stubs would
change the subject.

The emitted binary contains standard `try_table`, `throw`, and libc++abi's `__cxa_throw` /
`__cxa_begin_catch` functions. `wasmtime run -W exceptions=y,tail-call=y,function-references=y,gc=y
--invoke eh FVATest/Subjects/CppEH/eh.wasm 1` returns `-1515870812`, rc 0. The suite tests eight
bit patterns, including both unsigned endpoints and both signed-boundary sides. Wasmtime
`--invoke` takes signed decimal i32 arguments; the suite preserves the input bits when it
converts values above `2^31-1`.

## Fingerprint

Run `FVATest/Subjects/CppEH/fingerprint WASM`. The check reads the `wasm-tools print` text, so it
does not use FVA's decoder. It requires these properties:

- Each import is a function of `wasi_snapshot_preview1` among the 20 preview1 calls of the
  declared WASI profile (`.agent/spec.md`, Decisions: WASI).
- The exports are exactly `memory` and `eh`.
- The module contains at least one `try_table` and at least one `throw`.
- The module contains no legacy exception instruction: `try`, `catch`, `catch_all`, `delegate`
  or `rethrow`.

The check prints the counts. For the shipped file, it prints `imports 7 try_table 14 throw 1
throw_ref 2 catch 1 catch_ref 1 catch_all 11 catch_all_ref 1`. A build with
`-wasm-use-legacy-eh=true` fails the check: the SDK's runtime keeps `try_table`, but the source
adds legacy `try`, `catch` and `rethrow`.

## Lift

`Lifted.lean` is generated, never committed (it embeds the third-party bytes). It is the output
of this command:

```sh
lake exe fva lift FVATest/Subjects/CppEH/eh.wasm \
  FVATest/Subjects/CppEH/Lifted.lean --ns Subjects.CppEH.Lifted
```

`scripts/test-subjects` writes it (rewritten only when its bytes change). The kernel checks
`decode_eq` when the module builds, in about 130 s with 3.5 GB of memory.

## Run on the verified machine

`Run.lean` runs `eh` on the verified machine (`FVA.Wasm.Exec.Machine`) when the module builds. It
decodes `Lifted.bytes`, binds each import to a host function and instantiates the module once.
Each input then starts from the instantiated store, as a fresh process does. A stub host answers
`environ_sizes_get` with zero variables, as `wasmtime run` does without `--env`. A call to any
other import stops the run. The run checks 72 inputs: the eight bit patterns of the acceptance
oracle and 64 inputs from a fixed seed. Each result must match the source contract. Each odd input
must throw one exception and make one host call, and each even input must do neither.
`scripts/test-subjects` builds the module, and a result off the contract fails the step. The
claim's proof runs on the executable WASI host of U29b; `Run` keeps the stub as a control.

## System claim (U28g)

`Spec.lean` states `r1` (13 review lines; contract `docs/contracts/U28g-cpp-claim.md`). From one
fixed process start, every launch of `eh` on any 32-bit input `x` returns exactly `x + 1` for an
even `x` and `x` XOR `0xa5a5a5a5` for an odd `x`. The start has the argument `eh.wasm`, no
environment, an empty stdin, no preopened directory and every clock at 0. The world is the
reviewed WASI model restricted to the environment `E`, and memory growth that fits succeeds.
`Proof.lean` proves `r1` (`r1_proof`, domain witness `r1_domain`), and `fva trust` passes in
default and `--paranoid` mode. `Proof.lean` also proves `start_wf` and `eh_path`: on an odd input
the run ends with exactly one exception instance in its store, on an even input with none.
`Neg/Odd` and `Neg/Even` each change one result and fail at the kernel.

### Why a system claim

A C-ABI `Returns` claim does not fit this SDK artifact. `FVA/Spec/CAbi.lean` defines
`Instance m H s inst := Instantiated H m {} [] s inst`, explicitly for import-free modules.
The artifact's seven imports already block this claim form.

Even after imports are linked, an all-host claim is too strong. The real libunwind throwing
path calls `logAPIs`, then `getenv`, then `environ_sizes_get`. A diverging import prevents an
odd call from returning. The exported `eh.command_export` wrapper also calls
`__wasm_call_dtors` / `__stdio_exit`. The regular Wasmtime environment alone does not establish
host independence.

Run `FVATest/Subjects/CppEH/probe-host-boundary`. It registers a well-typed provider whose
`environ_sizes_get` loops. Its even-input positive control returns `1`, rc 0. With exactly the
same provider, input `1` reaches the infinite loop, timeout rc 124 after three seconds. The
probe itself returns 0 when both observations hold. This is a characterization probe, not a
gate that requires the host dependency to remain.

The claim is therefore `SysMust` under the declared WASI model and environment profile `E`, for
every input. The stock SDK runtime and the counterexample above stay; no replacement runtime
or stub enters the claim.
