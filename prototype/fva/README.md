# FVA prototype

FVA proves properties of compiled code. The proofs are about the real binary, so the source
language and the compiler need no trust. This prototype shows one path for any language that
compiles to WebAssembly:

1. A compiler (here `clang`) turns the source code into a `.wasm` file.
2. `fva lift` turns the `.wasm` bytes into a Lean value. The value is checked against FVA's
   WebAssembly semantics (`lean/FVA/Wasm/Semantics.lean`).
3. An agent writes the specification theorems and their proofs. The Lean kernel checks the
   proofs.
4. `fva trust` audits the result. It replays the proofs through the Lean kernel, finds the
   specification lines that a person must read, and rejects proofs that cheat. Add
   `--paranoid` to also replay the proofs through the independent kernels that ship with Lean.

## Run the demo

You need `uv`, Lean 4 with `lake` (version 4.35), and `clang` with the `wasm32` target.
Run this command:

```sh
cd prototype/fva && uv run fva demo
```

The demo does these steps:

- It compiles `examples/toy/toy.c` and compares the result with the pinned `toy.wasm`.
- It runs the lifted code in Lean and the real binary in wasmtime on the same inputs, and
  compares the results.
- It prints the trust report for `examples/toy`. The expected verdict is PASS.
- It prints the trust report for `examples/cheat`, which contains seven planted cheats. The
  expected verdict is FAIL.

## Read the example

- `examples/toy/Toy/Spec.lean` and `examples/toy/Toy/Def.lean` are the specification. They
  are the only files that a person must read. Each claim is a `Prop` definition.
- `examples/toy/Toy/Proof.lean` contains the proofs. Nobody must read them.
- `examples/cheat/Cheat/Spec.lean` describes each planted cheat.

The specification module must import only reviewed files. Thus a macro or a notation in an
unreviewed file cannot change what the specification says. The proofs import the
specification, and the specification never imports the proofs.

## Limits

- The semantics covers a subset of WebAssembly: 32-bit and 64-bit integer arithmetic,
  locals, `select`, and structured control flow. Memory, calls, globals, tables, and floats
  are not supported. `fva lift` stops with an error on any other instruction.
- The lifter (`src/fva/lift.py`) is part of the trusted base. The differential test is
  evidence for the semantics and the lifter, not a proof.
- The proofs for the toy functions were written by an agent in this session. `fva trust`
  makes no assumption about who wrote them.

## Commands

| Command | Purpose |
| --- | --- |
| `uv run fva lift <wasm> <out.lean> --ns <Namespace>` | Turn a `.wasm` file into a Lean module. |
| `uv run fva trust <project> [theorem ...]` | Build the project, audit it, and print the review surface. |
| `uv run fva difftest <project>` | Compare the Lean semantics with wasmtime. |

Add `--json` to any command to get machine-readable output for agents.
