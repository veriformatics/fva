# Verification of `lz4-c.wasm`

**Overall result: incomplete. R1, R2 and R3 have not been proved in full, and no counterexample to them was found.** The machine-checked results below are explicitly smaller claims. A PASS from FVA for these claims must not be read as certification of all the README requirements.

The artifact and source files have not been changed. No network access is needed for the checks.

## Requirement coverage

| Requirement | Machine-checked evidence | Remaining gap |
| --- | --- | --- |
| R1: all reads/writes stay in the permitted buffers | The case theorem checks unchanged source bytes and eight unchanged guard bytes immediately before and after each destination capacity. The zero-input theorem proves the **entire store** unchanged for every zero-input call. | **Unproved.** Guard observations do not establish read safety, exclude writes farther away, or exclude transient writes subsequently restored. There is no general access-trace invariant or proof for arbitrary malformed blocks, buffer placements, capacities, and caller memory. |
| R2: every valid independent block decodes correctly | The case theorem proves exact return values and exact output bytes for the valid blocks in cases 1–7 below, including the zero-capacity empty block. | **Unproved in general.** The theorem does not quantify over all valid blocks. No formal predicate for the complete English block format, or simulation from its decoding relation to all iterations of the compiled decoder, has been established. The interpretation of these examples as valid blocks is a manual format check. |
| R3: every nonnegative return corresponds to the permitted decoding | The case theorem proves exact output bytes and returns for the successful cases below, including offset-zero clearing and acceptance of an end-condition violation. The zero-input theorem excludes any successful return on zero-length input. | **Unproved in general.** There is no theorem extracting a sequence decomposition and its decoded content from every successful execution. In particular the two format departures allowed by R3 have only selected examples here. |

No failing input is claimed. The negative results in cases 9–12 are correct rejections, not counterexamples to R1–R3.

## Exact theorem statements

The public theorem statements in `Proofs/Proof.lean` are:

```lean
theorem zeroInputRejected_holds : zeroInputRejected
theorem regressionCases_holds : regressionCases
```

Their complete definitions, including all constants and postconditions, are in `Proofs/Spec.lean`. They use FVA's operational WebAssembly semantics, not a translation of the C source. The two propositions are exactly:

```lean
def zeroInputRejected : Prop :=
  Instantiable Lifted.module ∧
    ∀ H s inst, Instance Lifted.module H s inst →
      ∀ (src dst capacity : BitVec 32) (memory : List UInt8),
        CallReturns H (s.withBytes 0 memory) inst "LZ4_decompress_safe"
          [.i32 src, .i32 dst, .i32 0, .i32 capacity] fun s' vs =>
          s' = s.withBytes 0 memory ∧ vs = [.i32 4294967295]

def regressionCases : Prop :=
  Instantiable Lifted.module ∧ ∀ c ∈ cases, caseCorrect c
```

`4294967295` is the i32 bit pattern for signed `-1`. The first theorem permits *any* i32 source, destination and capacity, including arguments outside the README domain, and arbitrary caller bytes written from address zero. It proves total return and equality of the whole final and starting stores. It is an error-path theorem; it does not prove that a memory read never occurred.

For the second theorem, `cases`, `Case`, `caseCorrect`, `prepared` and `bytesAt` are defined in the same specification file. For every listed case, every fresh instance, and every host semantics, the caller writes the input at address **131072** and initializes the destination plus its two eight-byte guards to **165**. The destination starts at **196608**. FVA's `CallReturns` proves that **every execution terminates without trapping** and that the final state satisfies all of:

1. The return list is exactly the listed signed i32 result.
2. The output prefix is exactly the listed byte list.
3. Every source byte is unchanged.
4. Both eight-byte guards are unchanged.

The theorem has no fuel assumption. Its proof uses bounded computations as certificates, then applies FVA's proved `runDet_must`/`must_returned_of_runDet` bridge to total operational correctness. Every theorem also requires instantiability, so it cannot pass merely because no fresh instance exists. A private lemma in the proof establishes that every fresh instance equals the concrete initialized instance used for computation, including the actual global and data initialization.

### The concrete cases

All numbers in this table are decimal. `range(n)` denotes bytes `0,...,n-1`; repetition and concatenation have the exact Lean definitions shown in `cases`.

| Case | Input bytes | Capacity | Return | Output / interpretation |
| --- | --- | ---: | ---: | --- |
| 1 | `[0]` | 0 | 0 | Empty block and output; README R2's capacity exception. |
| 2 | `[0]` | 1 | 0 | Empty block with positive capacity. |
| 3 | `[16,65]` | 1 | 1 | One literal byte, `[65]`. |
| 4 | `[240,0] ++ range(15)` | 15 | 15 | Fifteen literal bytes; the required zero extension byte. |
| 5 | `[240,255,0] ++ replicate(270,65)` | 270 | 270 | 270 literal bytes; extension continuation through 255. |
| 6 | `[24,65,1,0,80,66,67,68,69,70]` | 18 | 18 | One literal 65, match offset 1 / length 12, then five final literals; output thirteen 65s followed by `[66,67,68,69,70]`. |
| 7 | `[131,0,1,2,3,4,5,6,7,8,0,80,20,21,22,23,24]` | 20 | 20 | Eight literals, match offset 8 / length 7, then five final literals; output `range(8) ++ range(7) ++ [20,21,22,23,24]`. |
| 8 | `[8,0,0,80,66,67,68,69,70]` | 17 | 17 | Offset 0 / length 12 produces twelve zero bytes, followed by the five literals; permitted by R3. |
| 9 | `[8,1,0,80,66,67,68,69,70]` | 17 | -4 | Offset 1 with no decoded prefix is rejected. No output prefix is specified on error. |
| 10 | `[240]` | 32 | -2 | Missing literal-length extension is rejected. |
| 11 | `[16]` | 1 | -2 | Missing literal byte is rejected. |
| 12 | `[]` | 1 | -1 | Zero-length compressed input is rejected. |
| 13 | `[0,0,0,80,66,67,68,69,70]` | 12 | 9 | Offset 0 / length 4 followed by five literals; output `[0,0,0,0,66,67,68,69,70]`. Last match starts only nine decoded bytes before the end; R3 allows acceptance of this end-condition violation. |

For each row, the input and destination buffers are nonnegative-sized, disjoint, and within the README address range. Guard bytes are deliberately outside the destination buffer. Source preservation and guard preservation are final-state observations, with the limitations described under R1.

## Connection to the shipped bytes

`Proofs/Lifted.lean` was generated by:

```sh
fva/.lake/build/bin/fva lift lz4-c.wasm Proofs/Lifted.lean --ns Proofs.Lifted
```

It contains the **8469** original bytes as one packed numeral, the decoded module (all six functions), the relative artifact path, and:

```lean
theorem decode_eq : decode bytes len = .ok module
```

The numeral and syntax were not edited. The original artifact's SHA-256 is:

```text
8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6
```

FVA checks that the file at `lz4-c.wasm` equals the lifted bytes, rechecks the generated file, and replays `decode_eq` along with the claims and proofs. The decoder is called through its actual export, function address 2. The proof does not recompile or assume correctness of `src/lz4.c`, `src/c-memory.c` or `build.sh`.

`verification/runtime_cases.py` additionally embeds the unchanged binary in a WAST script and instantiates small wrapper modules importing its memory and decoder. These wrappers set up the caller's buffers and inspect bytes; they do not replace the decoder. Wasmtime independently checks the same thirteen cases with **921 assertions**. This runtime check is finite corroboration, not a formal proof of any universal requirement.

## Reproduce offline

From this directory, with the supplied Lean/Mathlib/FVA build and tools on PATH:

```sh
bash verification/check.sh
```

The script checks the exact artifact hash, runs `lake build`, runs the wasmtime cases, copies the supplied unmodified FVA package into a temporary directory outside the project, points that copy at the already-installed dependency directory from `lake-manifest.json`, relinks its executable there, and runs:

```sh
"$audit_dir/.lake/build/bin/fva" trust "$project_dir" \
  --spec-module Proofs.Spec --root-module Proofs --surface-budget 100
```

Both variables are assigned by the script. The temporary copy is removed on exit. No cache download or dependency update is performed. The textual FVA verdict is saved in `verification/fva-trust.txt`. The originally supplied FVA distribution is the trusted baseline; copying and relinking it outside the project does not independently authenticate that distribution. Allow several minutes for kernel replay.

Success requires exit status 0 for the script, `lz4-c.wasm: OK`, a successful Lake build, `PASS: 13 cases, 921 runtime assertions on the unchanged artifact`, and FVA's `PASS` with accepted kernel replays and no reported issues. FVA's PASS applies **only to the two partial claims above**.

For the Lean build and runtime observations separately:

```sh
lake build
python3 verification/runtime_cases.py
```

These commands alone do not perform FVA's independent replay, artifact link audit, or trust audit.

## Review and trust

The project-specific mathematical review surface is `Proofs/Spec.lean`: the exact input cases, caller-state setup, observations and two limited propositions. Read that file together with the requirements and the coverage table. The English LZ4-format interpretations above are not independently formalized.

The unreviewed proof code uses ordinary kernel-checked proofs, symbolic execution with FVA's proved stepper, and `decide +kernel`/`kernel_rfl` for concrete computations. It introduces no custom axiom, `sorry`, native evaluation axiom, or substitute execution semantics. The generated lifted syntax and numeral are checked mechanically rather than assumed to model the binary.

The shared trust boundary is FVA's supplied, pinned specifications and audit glue, Lean 4.35.0's kernel and compiler, the independent replay kernel, and the pinned Mathlib v4.35.0 dependencies. FVA verifies the stepper and decoder against its specifications; it does not prove that its English-facing specifications capture every intended WebAssembly or LZ4 requirement. Python and wasmtime are additionally trusted only for the independent runtime observations.

The following sizes include comments and blank lines. The final FVA verdict is recorded below.

| Review/trust item | Files / physical lines / bytes | Role |
| --- | --- | --- |
| `Proofs/Spec.lean` | 1 / 79 / 3926 | All project-specific mathematical definitions and claims; primary human review. |
| `Proofs/Proof.lean` | 1 / 255 / 10986 | Kernel-checked proof code; no human assumption of its correctness is needed. |
| `Proofs/Lifted.lean` | 1 / 67 / 135649 | Generated artifact numeral, syntax and decoder theorem; mechanically linked and replayed. Long generated lines account for its size. |
| `Proofs.lean` | 1 / 1 / 20 | Imports the proof module for the final audit. |
| `lakefile.toml`, `lake-manifest.json` | 2 / 140 / 3981 | Build and pinned dependency configuration. |
| `verification/check.sh` | 1 / 35 / 1508 | Reproduction/orchestration script; read it if relying on the one-command check. |
| `verification/runtime_cases.py` | 1 / 72 / 3000 | Optional independent runtime evidence; inspect its duplicated cases, wrapper setup and assertions. |
| `README.md`, `lz4_Block_format.md` | 2 / 262 / 13555 | English requirements and format; needed to assess what the proved examples mean. |
| `fva/FVA/Spec/**/*.lean` | 23 / 3606 / 161903 | Supplied FVA mathematical trust boundary, reviewed once. |
| `fva/FVA/Trust/**/*.lean`, `fva/FVA/Tool/**/*.lean` | 17 / 3781 / 180528 | Conservative total for the supplied audit/orchestration glue, including tools not needed by this check. |

These are physical line/byte counts, including comments; the FVA verdict separately reports its reachable code-line review surface. The compiler, kernels, pinned dependencies and FVA base are shared infrastructure, not a claim that only the project-specific specification constitutes the whole trust boundary.

## Final checked run

On 2026-10-28, `bash verification/check.sh` exited **0**. The complete FVA output is in [verification/fva-trust.txt](verification/fva-trust.txt).

- `lake build`: success, with both theorem bodies checked.
- Wasmtime: **13 cases / 921 assertions passed** on the unchanged binary.
- Outside-built FVA: **PASS**, exactly the two intended claims, artifact link **matches**, no reported issues.
- FVA review surface: **52 code lines**, all in `Proofs.Spec` (79 physical lines including comments and blanks).
- Replay: **leanchecker accepted (315 s)**; **con-leche accepted (249 s)**.
- Axiom closures of both claims: only `propext`, `Classical.choice`, `Quot.sound`.
- The 72 pinned known-false canaries produced: leanchecker, 71 rejected and one acceptance covered by FVA's pinned known-acceptance policy; con-leche, 69 rejected and three declined, none accepted. Neither kernel crashed or timed out. FVA applied its supplied canary policy and returned PASS.

This verdict certifies the two stated partial claims. It does not discharge the missing R1–R3 obligations in the coverage table.
