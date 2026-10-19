# Verification of `sat_add`

## Result

All three README requirements are proved in Lean 4.35.0, for **every pair of
32-bit signed inputs**, both for a finite-width model of `sat_add.c` and for
execution of the decoded, shipped `sat_add.wasm`. No C or Wasm changes were needed.
The semantic-model boundaries are described below; this is not a proof of a
general-purpose C frontend or WebAssembly engine.

Only Lean's bundled `Init`, `Std`, and `Lean` libraries are used. There is no
Mathlib, network dependency, external solver, `sorry`, or native-evaluation axiom.

## Exact checking commands

From the repository root, with the installed Lean 4.35.0 toolchain:

```sh
./verify.sh
```

The script executes exactly:

```sh
lake clean
lake build
```

The clean step matters: `Artifacts.lean` reads the current C and Wasm files
during elaboration, and ordinary Lake caching does not track these included
files. Use `./verify.sh` after changing either artifact, rather than relying on
an incremental `lake build`.

The build checks all four Lean modules, including the axiom audit. Expected
output includes `Axiom audit passed for 21 theorems.` and
`Build completed successfully`. To print the audit again after building:

```sh
lake env lean Audit.lean
```

Both main correctness theorems depend only on Lean's standard logical axioms
`propext`, `Classical.choice`, and `Quot.sound`. `Audit.lean` rejects any other
transitive axiom dependency, including `sorryAx` and native-evaluation axioms.
Arithmetic proofs use kernel-checked lemmas and `omega`; constant checks use
`rfl` or kernel-reduced `decide`, not `native_decide` or `bv_decide`.

## What is proved

`BitVec 32` represents all 32-bit input bit patterns. Its `toInt` is the signed,
two's-complement interpretation. Sums in theorem statements use mathematical
Lean `Int`, so the requirements do not accidentally refer to wrapping addition.

Let `s = a.toInt + b.toInt`, `L = -2147483648`, and `U = 2147483647`.

| Requirement | Proven conclusion | C-model theorem | Shipped-module theorem |
| --- | --- | --- | --- |
| R1 | `L ≤ s ≤ U` implies result `= s` | `SatAdd.R1` | `SatAdd.Wasm.artifact_R1` |
| R2 | `U < s` implies result `= U` | `SatAdd.R2` | `SatAdd.Wasm.artifact_R2` |
| R3 | `s < L` implies result `= L` | `SatAdd.R3` | `SatAdd.Wasm.artifact_R3` |

Additional results:

- `SatAdd.c_correct` identifies the result with the independently expressed
  clamp `max L (min U s)`.
- `SatAdd.all_signed_inputs` states the result for arbitrary mathematical
  integers in the signed 32-bit range, proving coverage is not restricted to
  an accidental subset of integer inputs.
- `sum_bounds` proves `-4294967296 ≤ s ≤ 4294967294`.
- `addition_safe`, `widening_exact`, and `wideSum_exact` prove that widening
  preserves both operands, the addition fits signed 64 bits, and the actual
  finite-width addition equals the mathematical sum. In particular, C signed
  addition overflow cannot occur here.
- `lower_constant_safe` verifies the intermediate negation and subtraction in
  `-2147483647 - 1`. `final_cast_safe` and `narrowing_exact` establish that the
  last cast is reached only with a representable value and preserves it.
- `SatAdd.Wasm.artifact_eq_c` proves that decoded module execution returns
  `some (cSatAdd a b)` for every input. Thus it terminates with one result, with
  no invalid local access or stack failure in the modeled instruction semantics.
- `SatAdd.Wasm.artifact_correct` gives the clamp specification directly for
  the decoded module's execution result.

These are universal proofs, not input sampling or exhaustive test enumeration.

## Connection to the C source

`SatAdd.lean` manually models the small function using the **wasm32 ABI**:
32-bit signed `int`, 64-bit signed `long long`, and signed comparisons.
The model is a direct transcription of the expressions and control flow:

| C operation | Lean representation |
| --- | --- |
| `(long long)a + b` | `wideSum`: sign-extend both inputs to 64 bits, then perform `BitVec 64` addition |
| `s > 2147483647` | `max32 < s.toInt` |
| Return upper limit | `BitVec.ofInt 32 max32` |
| `s < -2147483647 - 1` | `s.toInt < min32`, with the constant expression proved safe and equal |
| Return lower limit | `BitVec.ofInt 32 min32` |
| `(int)s` | `BitVec.ofInt 32 s.toInt`, proved value-preserving on the reached branch |

The usual arithmetic conversions convert `b` to `long long` before addition;
the addition is **not** performed as a 32-bit operation. Comparison constants
are exactly representable when promoted to `long long`. No assumptions about
C signed wrapping or out-of-range narrowing are needed because the safety
lemmas rule out those cases.

`Artifacts.lean` uses `include_str` to read `sat_add.c` and proves
`SatAdd.source_matches`, equality to the exact source text transcribed above.
Consequently a fresh check rejects source drift, including whitespace changes.
This equality is a source binding, **not a verified C parser or a proof of the
manual translation itself**. The table and the small model expose that remaining
semantic correspondence for review.

## Connection to the shipped Wasm

The 87-byte module does not literally implement the C branches. Its optimized
function is:

```text
local.get 0; local.get 1; i32.add; local.tee 2
i32.const 31; i32.shr_s; i32.const -2147483648; i32.xor
local.get 2; local.get 1; i32.const 0; i32.lt_s
local.get 2; local.get 0; i32.lt_s; i32.xor; select; end
```

`Wasm.lean` supplies a deliberately restricted decoder and an executable stack
semantics for precisely the relevant instructions. The decoder checks the full
module prefix: magic/version, function type, function index, memory declaration,
exports, section/body sizes, and local declaration. It then decodes instructions
and immediates, requiring the final `end` and no trailing bytes. It is not a
general Wasm decoder; unsupported encodings fail.

`include_binary` in `Artifacts.lean` reads the actual file and embeds its bytes as
a Lean `List Nat` literal. `artifact_decodes` proves by kernel reduction that
these bytes decode to `program`. `invoke_program` symbolically executes every
instruction; `optimized_eq_c` proves that its bitwise result equals the C model.
Their composition is `artifact_eq_c`. Shift counts are masked modulo 32,
`i32.add` wraps modulo 2^32, `i32.lt_s` uses signed comparison and returns 0 or 1,
and `select` tests its i32 condition for nonzero.

Thus the shipped-artifact proof does not assume that Clang correctly compiled
the function. It verifies the decoded result independently. The handwritten
decoder's opcode/immediate interpretation and instruction semantics still need
to agree with WebAssembly; they have not been related to an external formal
WebAssembly specification.

## Checks performed and scope limits

The complete clean build and axiom audit passed on Lean 4.35.0. As a check on the
file bindings, temporary copies with an added C newline and with the Wasm
`i32.add` opcode changed to `i32.xor` were both rejected by the appropriate
binding theorem. The repository's original files were not modified.

Clang 23.1.1's wasm32 predefined macros confirmed 32-bit `int`, 64-bit
`long long`, and the signed limits used here. Rebuilding with the README command
also produced a byte-identical module. This compiler check is corroboration,
not a premise of the Lean artifact proof. It can be repeated after building:

```sh
clang --target=wasm32 -O2 -nostdlib -Wl,--no-entry -Wl,--strip-all -Wl,--export=sat_add -o .lake/build/rebuilt-sat_add.wasm sat_add.c
cmp sat_add.wasm .lake/build/rebuilt-sat_add.wasm
```

No README functional requirement remains unproved **within the stated models**.
Outside the proof are the manual C-to-model correspondence, conformance of the
restricted Wasm decoder/interpreter to the external language standard, general
compiler correctness, ABIs with different integer widths, actual execution
engine/hardware correctness, and module-instantiation resource availability.
The usual Lean kernel/toolchain and artifact-reading trust boundary also remains.
