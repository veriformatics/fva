# FVA — Formally Verify Anything

FVA checks formal proofs about the software that you actually ship. It reads the compiled WebAssembly file of a program, so the proofs are about the real binary and not about a model of the source code. For programs that it cannot verify as code, such as Python or R scripts, compilers and generators, FVA certifies each output that they produce.

FVA is a Lean 4 package. An AI agent writes the claims and the proofs; FVA makes them trustworthy and small to review:

- It measures the specification that a person must read. Every report states how many lines of claims and definitions you must review.
- It does not trust one proof checker. Each proof is checked again by an independent kernel, and each kernel is first tested on known false proofs.
- It links the proofs to the artifact. A changed byte in the `.wasm` file, or in a certified output file, makes the check fail.

Run `fva help` to see the commands, and `fva <command> --help` to see the arguments and options of one command.

## Requirements

- Lean 4.35.0 and Lake (`elan` installs them from `lean-toolchain`).
- Mathlib v4.35.0. The command `lake exe cache get` downloads its compiled files once; after that, FVA works offline.
- To compile examples: `clang` with the `wasm32` target, `rustc` with `wasm32-unknown-unknown`.
- For `fva explain`: a signed-in `codex` CLI.

## Start a project

1. Compile your code to WebAssembly (for example `clang --target=wasm32 -O2 -nostdlib -Wl,--no-entry -Wl,--export=f -o f.wasm f.c`).
2. Create the project:

   ```sh
   lake exe fva init myproof --lib MyProof --wasm f.wasm
   cd myproof && lake exe cache get && lake build
   ```

3. Write each claim in `MyProof/Spec.lean` as a `Prop` definition with a docstring that states its meaning in words. For example:

   ```lean
   /-- `clamp(x, lo, hi)` on signed 32-bit ints: `lo` below `lo`, `hi` above `hi`, else `x`. -/
   def clamp : Prop :=
     ∀ x lo hi : BitVec 32, Returns Lifted.module "clamp" [.i32 x, .i32 lo, .i32 hi]
       [.i32 (if x.slt lo then lo else if hi.slt x then hi else x)]
   ```

4. Prove each claim in `MyProof/Proof.lean` (an agent does this; `AGENT.md` explains the method). Nobody needs to read this file.
5. Check the result:

   ```sh
   fva trust . --spec-module MyProof.Spec --root-module MyProof
   ```

   `fva trust` prints PASS or FAIL, the reasons for a FAIL, and the files that you must review. Use an `fva` that you built outside the project for the final check, because a project can change its own copy.

## Certify outputs

To certify that a program's output is correct for its input, give FVA both files and a relation:

```sh
python3 sort.py < input.txt > output.txt
fva certify . --relation FVA.Cert.SortedPerm --input input.txt --output output.txt --ns Certs.Sorted
lake build && fva trust . --spec-module Certs.Sorted.Spec --root-module Certs.Sorted
```

The build fails when the output does not satisfy the relation. The certificate is about the exact bytes of the files: if the program prints a number in a different format, that is a different output.

## Read the claims in plain English

```sh
fva explain . --spec-module MyProof.Spec --root-module MyProof
```

`fva explain` writes a plain-English explanation of each claim, a table of example values (computed by Lean and by the real binary, never by the language model), and a check that the claim matches its docstring. It is a reading aid: the verdict comes from `fva trust`.

## What a PASS means

| layer | what it is | why you can rely on it |
|---|---|---|
| reviewed once | FVA's specifications: WebAssembly syntax, binary format, execution, integer and IEEE-754 arithmetic, claim forms, certificate relations, the verdict rules | short Lean definitions, audited against the WebAssembly 2.0 specification and tested against its official test suite and against wasmtime |
| verified implementation | the decoder, the reference interpreter, the floating-point operations, instantiation, the verdict function, the certificate checkers | proved correct against the specifications, and checked by a mutation test |
| trusted glue | reading facts from Lean, the file checks, process control, the external kernels | small and tested; each kernel must reject the known false proofs |
| residual trust | the Lean kernel (checked again by an independent kernel), the Lean compiler, Mathlib at its pinned revision | standard for Lean proofs |

Your review covers the claims in your specification files only. FVA's own files count as reviewed only when they are byte-identical to the pinned versions.

## Examples in this repository

- `FVATest/Examples/Toy`, `Mem`, `Rust`: C and Rust functions with loops, memory buffers, calls and `br_table`, proved on the compiled binaries.
- `FVATest/Certs`: certificates for the same sorted output from Python, R, Java and TypeScript programs, and for a toy compiler; files that must fail show what FVA rejects.

## Limits

- FVA verifies core WebAssembly 2.0 without SIMD, threads, exceptions or garbage-collected types.
- Programs that read files or the network through WASI are not modeled; certify their outputs instead.
- A proof shows that the binary meets the claims. It is your task to check that the claims say what you want.

## License

Apache-2.0 (`LICENSE`).
