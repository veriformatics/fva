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
`fva explain` also needs the `codex` CLI, signed in.
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

## Read a specification without Lean

You can use `fva explain` if you cannot read Lean. Run this command:

```sh
uv run fva explain examples/toy
```

For each claim, the report shows these items:

- The proof status from `fva trust`.
- An explanation of the claim in plain English, and the points that a reader can misread.
- A table of examples. Lean's compiled evaluator computes the value that the claim requires for each input, and
  wasmtime runs the real binary on the same input. A language model proposes the inputs, but
  it does not compute the values. The Lean kernel does not check these values. If a project
  overrides a definition with `implemented_by`, a value can differ from the claim, and
  `fva trust` rejects that project.
- An intent check. A second model call compares the explanation with the intent of the
  author. The intent is the docstring of the claim, or the name of the claim if there is no
  docstring.

The explanation reads the claim as Lean elaborates it, after all macros and notations. Thus a
macro that changes the meaning of a claim also changes the explanation. If a claim does not
have the form `∀ inputs, Returns …`, the report shows the elaborated claim instead of
examples.

The command saves the explanation in `fva-explain.json` in the project. Later runs show the
saved text and make no new model calls, so the text stays the same each time you read it.
The proof status is computed again on each run. If the specification, the binary, or the
prompts change, the report marks the saved text as STALE and the command returns 1. To
regenerate the text, add `--force`.

The explanation and the intent check come from a language model (`gpt-6-luna` through
`codex app-server`). They can be wrong. Use them to read the specification, and use
`fva trust` for the verdict. The command returns 0 only if `fva trust` passes and every
intent check matches.

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
| `uv run fva explain <project> [--force]` | Explain each claim in plain English, with computed examples and an intent check. Save the result, or show the saved result. |

Add `--json` to any command to get machine-readable output for agents.
