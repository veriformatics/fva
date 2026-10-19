# Verification result: R1 and R2 are false

The C source, README, and shipped `avg_floor.wasm` are unchanged.
The shipped module does **not** meet either requirement.

| Inputs `(a, b)` | Required floor average | Shipped result |
|---|---:|---:|
| `(2147483647, 2147483647)` | `2147483647` | `-1` |
| `(-2147483648, -2147483648)` | `-2147483648` | `0` |

These are Lean theorems about the shipped bytes, not just test results.
No sound proof that this implementation satisfies R1 or R2 can be supplied.
Instead, the proofs refute both requirements and characterize the entire input domain.

## One check command

From the repository root, run:

```sh
./verify.sh
```

This command needs no network, Mathlib, Lake package downloads, or Python packages.
It requires Python 3, Clang with wasm32/lld support, Node.js, Lean **4.35.0**, and
`leanexport`, `leanchecker`, `nanoda_bin`, and `con-ron` alongside the resolved Lean
executable. All are installed in the supplied environment. Missing tools, timeouts,
unexpected axioms, failed replays, and accepted false proofs fail the command.

**Exit zero means that the characterization, refutations, and checking controls
passed. It does not mean that the README requirements hold.**

Generated data, complete proof exports, tool binary hashes, diagnostic logs, review
statements, and size counts are placed in `.verification/`. Each run recreates this
directory. No cached proof object is used.

## What Lean proves

Inputs are integers restricted by `signed32 x := -2147483648 ≤ x ∧ x < 2147483648`.
This is exactly the signed 32-bit domain. `/ 2` below is integer Euclidean division, including negative inputs.
The theorem `floor_spec` proves its defining floor inequalities:

```text
2*q ≤ a+b < 2*(q+1), where q = (a+b)/2.
```

All theorem names have the `AvgFloor.` prefix in `verification/Proof.lean`.

| Theorem | Claim |
|---|---|
| `decoded` | The complete accepted module executes `((b + a).bmod 4294967296) / 2`. |
| `semantics` | The signed output is `((a + b).bmod 4294967296) / 2`. |
| `correct_iff` | The output equals the mathematical floor average **if and only if** `-2147483648 ≤ a+b < 2147483648`. |
| `fails_on_overflow` | Every pair whose mathematical sum is outside that range gives the wrong average. |
| `positive_counterexample`, `negative_counterexample` | The two exact results in the table above. |
| `not_R1`, `not_R2` | Negations of the universal requirement and its overflowing-input subset. |

Here `bmod 4294967296` maps an integer to its signed 32-bit representative.
The universal results cover all **2^64** input pairs; they do not depend on sampling.
The formal `R2` is the necessary overflowing-input subset emphasized by the
README; refuting it also refutes the README's stronger all-input claim.
The execution is total for this module: it produces a value for every input and
uses no memory, calls, or loops.

## Connection to the shipped implementation

1. The runner checks the original hashes of the C source, README, and binary.
2. It runs the README build command, changing only the output path:

   ```sh
   clang --target=wasm32 -O2 -nostdlib -Wl,--no-entry -Wl,--strip-all -Wl,--export=avg_floor -o .verification/rebuilt.wasm avg_floor.c
   ```

   It requires byte-for-byte equality with the shipped `avg_floor.wasm`.
3. It reads **all 64 bytes** of the shipped file and generates
   `.verification/lean/Artifact.lean`, a `List Nat` literal. There is no C-to-Lean
   translation and no replacement implementation.
4. `verification/Spec.lean` checks the exact 55-byte module envelope and total
   file length. The envelope includes the function type, function index, memory,
   export name and index, section lengths, body length, and local declarations.
   A small instruction interpreter then consumes every remaining byte.
5. The module body is:

   ```text
   local.get 1; local.get 0; i32.add; i32.const 1; i32.shr_s; end
   ```

   `i32.add` uses signed balanced remainder modulo 2^32. The interpreter supports
   `i32.shr_s` only when the stack's shift count is 1; its signed result is floor
   division by 2. It rejects all other shift counts and unsupported encodings,
   malformed stacks, incomplete bodies, and trailing instructions.
   `decoded` is proved by kernel reduction (`rfl`), not by trusting an external
   disassembler or executing compiled Lean code.

The small interpreter and fixed envelope are the semantic bridge that a human
must review against WebAssembly semantics. They are not a verified implementation
of the whole WebAssembly standard. The byte extraction, file I/O, compiler
invocation, and equality check are also part of the trusted binding infrastructure.
The compiler's general correctness is not assumed: only its checked reproduction
of this already-shipped byte image matters here.

Original SHA-256 values:

```text
avg_floor.c     8ddea065a9c9412f7b1ccd818ae22c04578dbe34ff9470c2b192df417777f5e0
avg_floor.wasm  551d0f840db799ed5ff513d8c47b0d2eaf2f01f662ff408e8f5df41b152c93ba
README.md      30efefdb54600854f010e44bca79f366d98285e8884c168838e398406d4e93e8
```

## Independent kernels and negative controls

The runner exports the selected theorems **with their complete proof dependency
closure**, then replays the same export from scratch through:

1. Lean's C++ kernel, via `leanchecker --from-export`.
2. **Nanoda**, an independently implemented Rust Lean kernel.
3. **Con-Ron**, a separate Rust checker, in its `--verified` mode.

Replaying with `leanchecker` is not counted as an independent implementation of
Lean's own kernel. Nanoda and Con-Ron provide the additional implementations.
No checker is allowed to skip an unsupported declaration or accept an unexamined
imported proof environment. The export axiom policy allows only `propext`,
`Quot.sound`, and `Classical.choice`. It rejects `sorryAx`, `Lean.trustCompiler`,
and any additional assumption, even if unused. Definitions must be safe.
There are no `sorry`, new axioms, `native_decide`, or unchecked evaluation proofs.

For each kernel, the check command first accepts valid proof files, then requires
type-error rejection of three well-formed, deliberately false exports:

- A proof of `True` relabeled as a proof of `False`.
- `Eq.refl 0` relabeled as a proof of `(0 : Nat) = 1`.
- The actual `not_R1` proof relabeled as a proof of `False`.

The forgeries retain the valid dependency environment. Rejection caused only by
a parser error, unsupported feature, unrelated crash, or timeout is not counted as success.
Nanoda's specific failed type-equality assertion (`self.def_eq(u, v)`, exit 101)
is its type-error rejection mechanism and is checked explicitly.
Separate controls check that the axiom policy rejects `sorryAx`,
`Lean.trustCompiler`, and an added assumption of `False`. Lean's frontend must
also reject `0 = 1` proved by `rfl`.

Two generated artifact mutations must invalidate the real Lean proof: changing
the addition opcode and changing the exported function index. The repository's
original files are never changed for these controls.

Node.js also executes the actual module on 4,217 deterministic boundary/random
pairs and checks the proven characterization. This corroborates the semantic
bridge; it is not a substitute for the universal proofs.

## Review surface and size

The project-specific semantic definitions are the six definitions in
`verification/Spec.lean` plus the generated byte literal `artifact`. There is no
custom arithmetic library, C parser, general module parser, or solver trusted as
an oracle. Review the complete Spec file, generated Artifact file, and the nine
theorem statements. Proof bodies need not be trusted; the kernels check them.

| Project review material | Lines, including blanks/comments | Bytes |
|---|---:|---:|
| Complete `Spec.lean` | 40 | 1,645 |
| Generated `Artifact.lean` (all 64 bytes) | 7 | 255 |
| Nine theorem statements, without proofs | 27 | 863 |
| **Project-specific total** | **74** | **2,763** |

The full `Proof.lean`, including checked proof bodies, is 55 lines / 1,620 bytes.
The table excludes inherited Lean definitions, which are counted separately below.

Exact source and transitive-dependency counts are reported by the check command
and saved in `.verification/sizes.json`. The transitive dependency list is
saved in `.verification/statement-dependencies.txt`; the theorem statements are
collected in `.verification/review-statements.txt`. Library dependencies are not
silently included in a claim that the project-only review surface is the entire
trusted base.

For this run, the transitive statement/definition closure contains **430 serialized
declaration records, 515 constant names, and 15,449 expression nodes**. This
includes library dependencies and compiler-generated auxiliaries. The census
starts at the nine theorem types, follows referenced definition bodies and other
dependencies, and counts inductive blocks as whole records. It excludes the nine
root proof bodies from this review census, but not from checking. The complete
proof export checked by every kernel is **95,958 NDJSON records / 4,866,403 bytes**.

The runner, shell entry point, control fixture, and WebAssembly runtime test are
additional auditable infrastructure: 393 lines / 17,300 bytes in total, separate
from the formal statements. The installed kernels,
standard-library meanings, axiom consistency, operating system, hardware, and
file binding remain trust assumptions. Multiple kernels and negative controls
reduce checker risk; they do not remove these assumptions.

## What is not proved

- R1 and R2 are **disproved**, not left as admitted goals. No source fix was made.
- This is not a proof of portable ISO C behavior. Signed `a + b` overflows for
  the counterexamples, which is undefined behavior in C; a negative signed right
  shift also depends on the C language version/implementation. The proved target
  is the shipped WebAssembly artifact specified by the README.
- The general Clang compiler, WebAssembly engines, the file-binding runner, and
  the interpreter's correspondence to the full WebAssembly standard are not
  formally verified here.
- The installed `lean4lean` binary cannot read this installation's `.olean`
  format. It is not used or counted among the successful independent replays.

## Exact proof-checking commands

`./verify.sh` runs every step, including the negative controls. Its central proof
commands are listed below for inspection; running only this subset omits controls.

```sh
export LEAN_PATH="$PWD/.verification/lean"
lean -DwarningAsError=true -o .verification/lean/Artifact.olean .verification/lean/Artifact.lean
lean -DwarningAsError=true -o .verification/lean/Spec.olean verification/Spec.lean
lean -DwarningAsError=true -o .verification/lean/Proof.olean verification/Proof.lean
```

Then replay the dependency-closed export:

```sh
B=$(dirname "$(readlink -f "$(command -v lean)")")
"$B/leanexport" Proof -- AvgFloor.floor_spec AvgFloor.decoded AvgFloor.semantics AvgFloor.correct_iff AvgFloor.fails_on_overflow AvgFloor.positive_counterexample AvgFloor.negative_counterexample AvgFloor.not_R1 AvgFloor.not_R2 > .verification/proofs.ndjson
"$B/leanchecker" --from-export .verification/proofs.ndjson
"$B/nanoda_bin" .verification/proofs-nanoda.json
"$B/con-ron" --verified --jobs=2 .verification/proofs.ndjson
```

The Nanoda configuration is generated by the runner. It enables Nat and String
kernel extensions and uses the exact axiom whitelist above. Logs retain each
checker's original verdict and diagnostic output.
