# C++ exception-handling subject

Contract = D29 / U28f in `.agent/spec.md`, Language + Wasm reach.
`eh.cpp` defines one function over every `uint32_t` input. Even inputs return their successor
modulo 2^32. Odd inputs throw that value and catch it in the same function. The catch returns
its bitwise XOR with `0xa5a5a5a5`. Unsigned arithmetic has no signed-overflow case.

## Build

Run `FVATest/Subjects/CppEH/build`. It uses the pinned `.tools/wasi-sdk`. Set `WASI_SDK_PATH`
only when the SDK is at another path. An optional output path keeps the shipped file unchanged.

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

## Proof seam

Expected generated module = `FVATest/Subjects/CppEH/Lifted.lean`, namespace
`Subjects.CppEH.Lifted`. Generate it with:

```sh
lake exe fva lift FVATest/Subjects/CppEH/eh.wasm \
  FVATest/Subjects/CppEH/Lifted.lean --ns Subjects.CppEH.Lifted
```

`Spec.lean` records the provisional goal `r1 : ∀ x : BitVec 32, Returns …`, with no input
restriction. The expected proof root is `FVATest.Subjects.CppEH.Proof`, with a theorem whose
type is `Subjects.CppEH.r1`. The suite checks lift support and both default / paranoid trust.
Lift and proof modules are absent on the pre-EH revision. Eight calls do not prove the goal.

## System claim pending U27+U29b

The provisional `Returns` goal does not fit this SDK artifact. `FVA/Spec/CAbi.lean` defines
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

The selected form is a system claim: `SysMust` under the declared WASI model and environment
profile `E`, for every input. The claim must state the environment contents; a profile that
excludes `LIBUNWIND_PRINT_APIS` can disable the logging branch without changing the runtime.
The stock SDK runtime and this counterexample stay. U28f covers build, lift and EH execution;
the all-input proof follows the WASI model and executable host.

The formal statement stays pending U27+U29b. MAIN must supply the exact imported-module/system
vocabulary before `Spec.lean` is rewritten blind. Its current `Returns` draft is false for the
artifact and is explicitly non-binding, not a ready-to-prove acceptance claim. No public API,
environment default, replacement runtime or stub is invented in its place.
