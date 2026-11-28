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
- For `fva trust` and `fva explain`: `bwrap` (bubblewrap) 0.8 or later, with unprivileged user namespaces. An older or setuid `bwrap` still runs the sandbox, but it cannot stop the project's code from creating user namespaces, and `fva trust` tells you so.
- For `fva explain`: a signed-in `codex` CLI.

## Start a project

1. Compile your code to WebAssembly (for example `clang --target=wasm32 -O2 -nostdlib -Wl,--no-entry -Wl,--export=f -o f.wasm f.c`).
2. Create the project:

   ```sh
   lake exe fva init myproof --lib MyProof --wasm f.wasm
   cd myproof && lake exe cache get && lake build
   ```

3. Write each claim in `MyProof/Spec.lean` as a `Prop` definition marked `@[fva_claim]`, with a docstring that states its meaning in words. A `Prop` definition without the mark is a helper: `fva trust` does not prove it, and its report lists it apart. For example:

   ```lean
   /-- `clamp(x, lo, hi)` on signed 32-bit ints: `lo` if `x < lo`, else `hi` if `x > hi`, else `x`
   (tested in this order, so with `lo > hi` the result is `lo` for `x < lo` and `hi` otherwise). -/
   @[fva_claim] def clamp : Prop :=
     ∀ x lo hi : BitVec 32, Returns Lifted.module "clamp" [.i32 x, .i32 lo, .i32 hi]
       [.i32 (if x.slt lo then lo else if hi.slt x then hi else x)]
   ```

4. Prove each claim in `MyProof/Proof.lean` (an agent does this; `AGENT.md` explains the method). Nobody needs to read this file.
5. Check the result:

   ```sh
   fva trust . --spec-module MyProof.Spec --root-module MyProof
   ```

   `fva trust` prints PASS or FAIL, the reasons for a FAIL, and the files that you must review. Use an `fva` that you built outside the project for the final check, because a project can change its own copy.

## State what one call returns

To state and prove what one call of an exported function returns, give FVA the inputs:

```sh
fva call MyProof/Lifted.lean iround f64:0x3fdfffffffffffff --spec Calls/Spec.lean --proof Calls/Proof.lean
lake build && fva trust . --spec-module Calls.Spec --root-module Calls.Proof
```

FVA runs the call with its reference interpreter. Then it writes the claim of the result and a proof that the kernel checks. Give an integer argument as `i32:<n>` or `i64:<n>`. Give a float argument as its bits, for example `f64:0x3fe0000000000000`. This command supports modules without imports, globals, element or data segments, or a start function. A wrong result of one call is often the shortest proof that a requirement fails.

## Certify outputs

To certify that a program's output is correct for its input, give FVA both files and a relation:

```sh
python3 sort.py < input.txt > output.txt
fva certify . --relation FVA.Cert.SortedPerm --input input.txt --output output.txt --ns Certs.Sorted
lake build && fva trust . --spec-module Certs.Sorted.Spec --root-module Certs.Sorted
```

The build fails when the output does not satisfy the relation. The certificate is about the exact bytes of the files: if the program prints a number in a different format, that is a different output.

## Run a WASI program

FVA can run a WASI command on its verified machine with its verified WASI host:

```sh
fva run program.wasm --dir data::/data --env LANG=C -- input.txt
```

The program gets the arguments after `--`, with the module's file name as argument 0. FVA reads standard input and each `--dir` directory before the program starts. It writes the changed files back when the program stops, also when the program fails. The exit status is the program's status. A status from 126 on is reported as 1, a trap as 134, and an exception that no handler catches as 1. Status 2 means that FVA could not run or finish the program, and the message names the cause. FVA writes at most one message of its own. The message starts with `fva run: ` and comes after all the output of the program on standard error. Run `fva run --help` for the options.

FVA supports the 20 WASI preview1 calls that C and C++ programs built with wasi-sdk use: `args_get`, `args_sizes_get`, `environ_get`, `environ_sizes_get`, `clock_time_get`, `fd_close`, `fd_fdstat_get`, `fd_fdstat_set_flags`, `fd_prestat_get`, `fd_prestat_dir_name`, `fd_read`, `fd_seek`, `fd_write`, `path_create_directory`, `path_filestat_get`, `path_open`, `path_remove_directory`, `path_unlink_file`, `proc_exit` and `random_get`. A module that imports other functions does not run. The reviewed specification `FVA/Spec/Wasi` states what these calls may do (WITX allows many results) and the host `E` that claims assume: the results of wasmtime 50.0.0, with these differences:

- Rights: FVA checks the rights of each descriptor and reports them as the program requested them. A preopened directory has wasmtime's rights plus `fd_datasync`, `fd_sync` and `path_filestat_set_size`. Wasmtime does not check most rights and reports fixed values.
- File status: the serial number is the file's index + 1, the link count is 1, and the times are 0.
- Clocks: `fva run` reads 0 on every clock. A claim states the clock readings that it assumes.
- Files can grow to 2^63 − 1 bytes, as on a Linux tmpfs. Other file systems stop earlier.
- Reads and writes transfer the first non-empty buffer, and a read from standard input returns at most 65,536 bytes.
- A call fails only for the reasons that the specification states. There are no I/O or resource errors.
- `fva run` reads standard input and the directories completely before the run, and changes the host files only at the end. The directories must contain regular files and directories only, without symbolic links or hard links.
- When a step has more than one allowed result (the payload of a NaN), `fva run` stops with status 2.
- With `--random`, every `random_get` call gets the given bytes, and the message of FVA says so.

The full list, with sources, is in `docs/contracts/U29a-wasi.md` and `docs/contracts/U29b-host.md`. FVA checks `fva run` against wasmtime on a pinned selection of the WASI test suite (`FVATest/Wasi/testsuite`) and on a corpus of 116 small programs (`FVATest/Wasi/run`).

## Read the claims in plain English

```sh
fva explain . --spec-module MyProof.Spec --root-module MyProof
```

`fva explain` writes a plain-English explanation of each claim, a table of example values (computed by Lean and by the real binary, never by the language model), and a check of the claims against your requirements. It is a reading aid: the verdict comes from `fva trust`.

Write the requirements in `requirements.md` beside the spec module, in your own words. Start each requirement with a `## <id>` line:

```markdown
## R1
clamp(x, lo, hi) returns lo when x < lo, hi when x > hi, and x otherwise.
```

An agent can draft this file from the README, the issues or the source code. Read and approve it before you rely on the result: it is the reference that the claims are checked against. The model explains the claims without their names and docstrings, so a claim that is named `clamp` but returns `x` gets the verdict DIFFERENT. Without a requirements file, each claim is compared with its own docstring, which its author wrote.

## What a PASS means

| layer | what it is | why you can rely on it |
|---|---|---|
| reviewed once | FVA's specifications: WebAssembly syntax, binary format, execution, integer and IEEE-754 arithmetic, claim forms, certificate relations, the verdict rules | short Lean definitions, audited against the WebAssembly 2.0 specification and tested against its official test suite and against wasmtime |
| verified implementation | the decoder, the reference interpreter, the floating-point operations, instantiation, the validator (a validated module never gets stuck), the verdict function, the certificate checkers | proved correct against the specifications, and checked by a mutation test |
| trusted glue | reading facts from Lean, the file checks, process control, the external kernels | small and tested; each kernel must reject the known false proofs |
| residual trust | the Lean kernel (checked again by an independent kernel), the Lean compiler, Mathlib at its pinned revision | standard for Lean proofs |

Your review covers the claims in your specification files only. `fva trust` fails when one of these files runs code or changes how Lean reads the rest of it (for example `#eval`, `run_cmd`, `#exit` or `set_option`), because the text that you read would then not be the statement that the kernel checks. FVA's own files count as reviewed only when they are byte-identical to the pinned versions.

## Examples in this repository

- `FVATest/Examples/Toy`, `Mem`, `Rust`: C and Rust functions with loops, memory buffers, calls and `br_table`, proved on the compiled binaries.
- `FVATest/Certs`: certificates for the same sorted output from Python, R, Java and TypeScript programs, and for a toy compiler; files that must fail show what FVA rejects.
- `FVATest/Subjects`: results about published software, each checked by `fva trust`. They include counterexamples for a hand-written LZ4 codec in WebAssembly, measured against a reviewed specification of the LZ4 block format. They also include a proof for every input of lz4's `LZ4_decompress_safe` in its shipped WebAssembly build: each call reads and writes only its two buffers and returns, a valid block decodes to its content, and a non-negative result means that the input parsed as LZ4 sequences (a 76-line specification, checked in the default and `--paranoid` modes). They include a proof for every input of edgeR's counts-per-million function in its shipped WebAssembly build, certificates that refute RNAnorm's claim that its TMM factors match edgeR's to 10 decimal places, and a counterexample for GLM's `iround`.

The third-party binaries that these results are about are not in this repository, and neither are the archived benchmark runs. `scripts/fetch-subjects` and `bench/fetch-runs` download them from the releases of [veriformatics/fva-artifacts](https://github.com/veriformatics/fva-artifacts), and each download is checked against its pinned SHA-256 in `bench/subjects/manifest.json`. The gate runs these scripts for you.

## Benchmark

`bench/results.md` compares AI agents that work with FVA, without it, with FVA's principles in the prompt only, and with an established verifier (Frama-C or Verus). There are six tasks and five runs per agent setup. The results are mixed, and the file reports losses as losses:

- In every task, every agent that used FVA produced a machine-checked statement about the shipped binary or output files. The other agents did this only in some tasks, with an extractor and semantics that they wrote themselves and must be trusted.
- FVA did not save time or cost. Agents with FVA used 3 to 11.5 times as many input tokens as agents with only the task.
- On two tasks without a known defect (the LZ4 decoders in C and Rust), the agents with FVA proved less about memory access than the other agents. At the time of the benchmark, FVA had no reviewed claim form for memory access. It has one now: `CallWithin` states the bytes that a call may read and write at every step, and the proof of the lz4 C decoder uses it.
- On the GLM task, every agent found the wrong result for `0.49999999999999994`. Only the agents with FVA proved it about the shipped binary, in a statement of 9 to 12 lines.
- FVA was developed with these tasks known.

## Limits

- FVA verifies core WebAssembly 2.0 without SIMD, threads, exceptions or garbage-collected types.
- FVA models 20 WASI preview1 calls (see Run a WASI program). For programs that use other WASI calls or the network, certify their outputs instead.
- A proof shows that the binary meets the claims. It is your task to check that the claims say what you want.
- `fva trust` and `fva explain` run the project's own code (its Lake configuration, its build, its Lean definitions) in a `bwrap` sandbox: no network, no new user namespaces, the system read-only, your home directory hidden, and writes allowed only in the project's `.lake` directories. The project needs a `lake-manifest.json`. Inside an agent's sandbox that denies network sockets, `fva trust` keeps its sandbox without its own network namespace and says so; where bwrap cannot run at all, `--no-sandbox` runs without it (use it only inside a container you trust). FVA itself still reads the project's compiled `.olean` files. FVA builds the spec module and the project modules that it imports again, in the same sandbox, and the check fails if the project's compiled files are different. If you do not trust a project, run FVA inside a container or a virtual machine as well.

## License

Apache-2.0 (`LICENSE`).

The benchmark archive is a privacy edition. It removes personal machine labels, including labels inside compressed event logs. Scientific source files, license notices, and numeric results are unchanged. Historical machine paths remain nonportable. This export is not a new benchmark run.
