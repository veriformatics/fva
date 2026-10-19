## Intent

FVA (Formally Verify Anything) aims to follow a software development tooling trend brought on by REA (Reverse Engineer Anything): https://github.com/morluto/rea. Our goal is to allow a user to apply FVA to any pre-existing or new project and find a path towards formal verification of it. It is important that the formal verification is directly linked to the code of the software's actual implementation, for instance Verus is tightly integrated with Rust, and Lean allows for metaprogramming. For other languages, we may have to develop our own solutions and it is best if we can find a unified approach to avoid an excess of language-specific handling, which is likely to be brittle and inelegant in approach.

Like REA, FVA should be readibly usable by an AI agent that requests it, and that is the primary target. FVA uses extensive AI-generated proofs to achieve its verification claims. At the same time FVA should aim to minimize the surface of human-reviewable spec. This is treated as an optimization problem: provided a minimally sufficient spec, and a trusted kernel like that of Lean's, we can assume that an unbounded amount of proofs can be used to verify correctness of a program. See https://github.com/schildep/verified-3d-mesh-intersection, for an excellent example of this approach. Spec review may be further simplified by informalization back into natural language (https://github.com/metareflection/claimcheck); we must be open to considering alternative and supplementary approaches at all times.

## Artifacts

- `prototype/fva/` = PROTOTYPE: Python (uv) CLI `fva` + Lean 4 core package `prototype/fva/lean` (WASM semantics + trust-audit metaprogram) + worked examples `prototype/fva/examples/`.
  - Run: `cd prototype/fva && uv run fva demo` = compile toy C → wasm, lift → Lean, check proofs, differential-test semantics vs wasmtime, print trust report for `examples/toy` (green) + `examples/cheat` (red).
  - Subcommands: `uv run fva lift <wasm> <out.lean> --ns <Ns>`, `uv run fva trust <lake-dir> <theorem>… [--json]`, `uv run fva difftest <lake-dir> <wasm>`.

## Decisions

- Link path = WASM lift: any source language → wasm (compiler + source untrusted) → `fva lift` → Lean AST value over FVA's WASM semantics; theorems quantify over that lifted value; the `.wasm` = the verified artifact, committed + sha256-pinned inside the lifted file.
- Trusted base = Lean kernel + axioms {propext, Classical.choice, Quot.sound} + FVA WASM semantics (shared across every project/language, reviewed once) + lifter.
- Human-review surface = statement closure of the target theorems: constants their types mention, transitively through definition bodies, excluding subject (lifted code), FVA base + Lean core; `fva trust` computes it + counts lines.
- Trust audit fails on: non-standard axiom (incl. `sorryAx`, `Lean.ofReduceBool`), `implemented_by`/`extern`/`unsafe`/`partial`/`opaque` in theorem closure, theorem statement not mentioning a subject, lifted file ≠ re-lift of pinned wasm.
- Prototype stack = Python via uv + Lean 4.35 core, no Mathlib.
- Prototype scope = trust audit + one worked example; survey/plan, claimcheck-style informalization, MCP/skill packaging = later phases.

## Tasks

- [ ] Lean package: WASM subset semantics (i32/i64, locals, select, block/loop/if/br/br_if/return, fuel interpreter, `Returns`)
- [ ] Python lifter: wasm binary → Lean `Module` value + sha256 pin
- [ ] Toy example: clamp/gcd/sum_to C → wasm → spec + proofs
- [ ] Trust metaprogram + `fva trust` report (text + JSON)
- [ ] Differential test vs wasmtime + `fva demo`; cheat example (red path)
- [ ] Run artifacts, review, deferred rows, Phase → ITERATE
- See `.agent/deferred.md` for the deferral queue.

## Phase

PROTOTYPE — whole product
