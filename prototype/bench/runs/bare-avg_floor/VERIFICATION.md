# Verification result: requirements are false

The original `avg_floor.c` and shipped `avg_floor.wasm` are unchanged. It is
impossible to prove that they satisfy R1/R2: Lean proves counterexamples to both.
The verification uses Lean **4.35.0** and its bundled standard library only;
there is no Mathlib, external package, network dependency, `sorry`, `admit`,
custom axiom, or `native_decide` in the proofs.

## Check the proofs

Run these commands **from the repository root**:

```sh
lean --version
lake clean
lake build
lake exe verify
lake env lean ./Audit.lean
```

All commands were run successfully. `lake build` elaborates and kernel-checks
the proofs and builds the file-identity checker. `lake exe verify` checks the
current C source and **every byte** of the current Wasm artifact against the
proved snapshots. Its successful output explicitly says R1/R2 are **REFUTED**;
exit status zero means the verification/checks succeeded, not that the code is
correct.

`Audit.lean` prints the axioms used transitively by the main theorems. The only
ones reported are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`
(some theorems use fewer or none). There are no application-specific axioms or
`sorryAx`. All computational proof steps use kernel-reducible `decide`, not
native-code evaluation as a proof oracle.

The clean build matters: the source/artifact are embedded during elaboration,
and Lake need not notice edits to files embedded by an elaborator. The runtime
identity checker additionally rejects changed files even with cached proofs.

## What is proven

Let `a` and `b` be arbitrary signed 32-bit inputs, `s` their **unbounded integer**
sum, and `q = floor(s / 2)`.

| Requirement | Machine-checked result |
| --- | --- |
| R1: return `floor((a+b)/2)` for every input | **False:** `not_R1` and `Artifact.artifact_violates_R1`. |
| R2: correct even when the sum does not fit in 32 bits | **False:** `not_overflow_requirement` and `Artifact.artifact_violates_R2` refute its explicitly required overflowing-input case. |

Names below are in namespace `AvgFloor`, with `Artifact` where indicated.

### Specification and complete behavior

- `input_range` and `encoding_covers_signed_inputs`: `BitVec 32` with signed
  interpretation covers exactly the mathematical signed-32-bit inputs.
- `specification_is_floor` and `specification_unique`: the specification is
  exactly the unique integer `q` satisfying `2*q ≤ s < 2*(q+1)`. In particular,
  negative odd sums round down, not toward zero.
- `specification_fits`: the required answer always fits in signed 32 bits.
- `wasmAvg_toInt`: the implementation returns the floor of half the **wrapped**
  signed-32-bit sum, not generally half the mathematical sum.
- `all_input_behavior`: for **every** pair of input words, the signed result is

  ```text
  q + 2147483648,  if s < -2147483648
  q - 2147483648,  if s >  2147483647
  q,              otherwise.
  ```

- `correct_iff_no_overflow`: correctness holds **if and only if**
  `-2147483648 ≤ s ≤ 2147483647`. Thus every overflowing sum gives an incorrect
  result, by exactly `2^31`.
- `Artifact.artifact_execution`: for all input words, execution of the decoded
  shipped artifact terminates without a stack failure and returns `wasmAvg`.
- `Artifact.artifact_correct_iff`: the same necessary-and-sufficient condition
  for the artifact, rather than just the arithmetic expression.
- `Artifact.artifact_correct_iff_integer_inputs`: that artifact theorem stated
  directly for arbitrary mathematical integers `a`, `b` within signed-32-bit
  bounds.

### Concrete counterexamples

These are Lean theorems, not just test results:

| Inputs | Mathematical sum | Required answer | Wasm answer | Theorem |
| --- | ---: | ---: | ---: | --- |
| `INT_MAX, INT_MAX` | 4294967294 | 2147483647 | -1 | `max_counterexample` |
| `INT_MIN, INT_MIN` | -4294967296 | -2147483648 | 0 | `min_counterexample` |
| `INT_MAX, 1` | 2147483648 | 1073741824 | -1073741824 | `max_plus_one_counterexample` |

`Artifact.artifact_counterexample` also proves the first counterexample directly
through decoding/execution of the embedded artifact. `negative_odd_example`
checks `(-1, 0) → -1`, illustrating the floor convention. Executing the real
module in Node's WebAssembly engine independently reproduced the three failing
examples and the negative-rounding case; those runs are sanity checks, not the
universal proof.

### C definedness

The C expression performs signed `int` addition **before** shifting. On the
32-bit-int target, a nonrepresentable sum is signed-overflow undefined behavior
at the C level. WebAssembly's modular `i32.add` does not make that C operation
defined.

`cTargetEval` is a partial, target-specific model: it returns `none` for signed
addition overflow, and otherwise applies arithmetic signed right shift.

- `c_defined_iff`: this model is defined exactly when the sum fits in `int32`.
- `c_correct_when_defined`: every defined result meets the floor specification.
- `c_wasm_agree_when_defined`: the C target model and artifact model agree on
  the defined domain.
- `c_overflow_counterexample`: `(INT_MAX, INT_MAX)` is undefined in that C model.

Arithmetic right shift of negative signed values is a target choice (and
implementation-defined in C17), not a portable-C assumption silently built into
the requirements. The actual compiled artifact uses `i32.shr_s`.

## How the proofs connect to the files

### C source

`Artifact.sourceSnapshot` uses Lean's `include_str` to read the source at
elaboration time. `source_matches` proves exact equality to the original:

```c
/* Average of two 32-bit signed integers, rounded down. */
int avg_floor(int a, int b) { return (a + b) >> 1; }
```

`AvgFloor.lean` manually models that expression's signed-addition definedness
and the target's shift operation. **Source equality pins the reviewed code;
it is not a verified C parser or a C-to-Lean translation theorem.**

### Shipped WebAssembly

`EmbedBytes.lean` supplies a small binary-file elaborator. It reads raw bytes and
emits an ordinary literal `List Nat` into the Lean term; it introduces no axiom.
`Artifact.binary_matches` kernel-checks equality of the embedded file with the
complete expected 64-byte module, including its header, types, memory, exports,
and code.

The fixed prefix describes a module with no imports or start function, one
function of type `(i32, i32) → i32`, and export `avg_floor` referring to function
0. `decodeModule` requires that exact 55-byte prefix and total length 64;
`decodeInstructions` decodes the remaining bytes:

```text
offset  bytes    instruction
0x37    20 01    local.get 1
0x39    20 00    local.get 0
0x3b    6a       i32.add
0x3c    41 01    i32.const 1
0x3e    75       i32.shr_s
0x3f    0b       end
```

`decode_binary` proves decoding yields precisely that program. `step`/`execute`
give a small stack semantics: modular 32-bit addition, signed right shift with
the shift count reduced modulo 32, parameter lookup, and stack checks.
`program_execution` and `artifact_execution` connect its execution to the
arithmetic model. Unsupported encodings and instructions are rejected; this is
deliberately not a general Wasm parser/validator.

The original file hashes, for identification (identity checks do not rely on
hashes), are:

```text
avg_floor.c     8ddea065a9c9412f7b1ccd818ae22c04578dbe34ff9470c2b192df417777f5e0
avg_floor.wasm  551d0f840db799ed5ff513d8c47b0d2eaf2f01f662ff408e8f5df41b152c93ba
```

As a separate reproducibility check, the README build command with installed
Clang 23.1.1 produced a byte-for-byte identical artifact. To repeat it without
overwriting the shipped file:

```sh
mkdir -p .lake
clang --target=wasm32 -O2 -nostdlib -Wl,--no-entry -Wl,--strip-all \
  -Wl,--export=avg_floor -o .lake/avg_floor.rebuilt.wasm avg_floor.c
cmp avg_floor.wasm .lake/avg_floor.rebuilt.wasm
llvm-objdump -d avg_floor.wasm
```

## Limits and unproved claims

- **R1 and R2 cannot be proven for the supplied implementation: they are
  disproven.** No repair, changed requirement, overflow assumption, or widened
  addition has been substituted for the original code.
- The C model, restricted Wasm decoder/semantics, and interpretation of the
  fixed module prefix are handwritten. They are inspectable and mechanically
  connected to the exact files, but not derived from a separately verified
  complete C or official WebAssembly semantics.
- The compiler, linker, WebAssembly engine, operating system, and hardware are
  not verified. The byte-level artifact proof does not require a compiler
  correctness theorem; the byte-identical rebuild is empirical evidence only.
- Lean's kernel/standard axioms and correct loading of local files are trusted.
  The binary elaborator only supplies literal data; the runtime identity check
  separately compares the actual on-disk bytes with the pinned data.

The successful result is therefore a **machine-checked refutation plus an exact
correctness-domain proof**, not a claim that this defective library satisfies
its README.
