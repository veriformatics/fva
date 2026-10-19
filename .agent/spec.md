## Intent

FVA (Formally Verify Anything) aims to follow a software development tooling trend brought on by REA (Reverse Engineer Anything): https://github.com/morluto/rea. Our goal is to allow a user to apply FVA to any pre-existing or new project and find a path towards formal verification of it. It is important that the formal verification is directly linked to the code of the software's actual implementation, for instance Verus is tightly integrated with Rust, and Lean allows for metaprogramming. For other languages, we may have to develop our own solutions and it is best if we can find a unified approach to avoid an excess of language-specific handling, which is likely to be brittle and inelegant in approach.

Like REA, FVA should be readibly usable by an AI agent that requests it, and that is the primary target. FVA uses extensive AI-generated proofs to achieve its verification claims. At the same time FVA should aim to minimize the surface of human-reviewable spec. This is treated as an optimization problem: provided a minimally sufficient spec, and a trusted kernel like that of Lean's, we can assume that an unbounded amount of proofs can be used to verify correctness of a program. See https://github.com/schildep/verified-3d-mesh-intersection, for an excellent example of this approach. Spec review may be further simplified by informalization back into natural language (https://github.com/metareflection/claimcheck); we must be open to considering alternative and supplementary approaches at all times.

## Artifacts

- `prototype/fva/` = PROTOTYPE: Python (uv) CLI `fva` + Lean 4.35 core package `prototype/fva/lean` (WASM semantics, proof support, `fva-trust` metaprogram) + worked examples `prototype/fva/examples/{toy,cheat}`; human entry = `prototype/fva/README.md`.
  - Run: `cd prototype/fva && uv run fva demo` = rebuild toy C → wasm vs pinned sha, difftest Lean semantics vs wasmtime, trust report `examples/toy` (PASS) + `examples/cheat` (FAIL); rc 0 = all as expected.
  - Subcommands: `uv run fva lift <wasm> <out.lean> --ns <Ns>`, `uv run fva trust <lake-dir> [theorem…] [--spec-module M] [--paranoid] [--json]`, `uv run fva difftest <lake-dir>`.
  - Needs: uv, Lean 4.35 + lake (bundles `leanexport`, `lake check`, nanoda/con-leche/con-ron for `--paranoid`), clang wasm32 target.

## Decisions

- Link path = WASM lift: any source language → wasm (compiler + source untrusted) → `fva lift` → Lean `Module` value over FVA's WASM semantics; theorems quantify over that value via `Returns`; the `.wasm` = the verified artifact, committed + sha256-pinned in the lifted file; `fva trust` re-lifts + byte-compares.
- Trusted base = Lean kernel + axioms {propext, Classical.choice, Quot.sound} + `FVA/Wasm/Semantics.lean` (shared across every project/language, reviewed once) + `src/fva/lift.py`; difftest vs wasmtime = evidence for semantics + lifter, not proof.
- Human-review surface = statement closure of the spec theorems: constants their types mention, transitively through definition bodies, stopping at subject (lifted code), FVA base + Lean core; `fva trust` computes it + counts code lines.
- Spec layout per project (mesh-repo pattern): `<Lib>/Def.lean` vocabulary + `<Lib>/Spec.lean` theorem statements (review surface), `<Lib>/Proof.lean` (never read), `<Lib>/Lifted.lean` (generated).
- `fva trust` FAIL on: non-standard axiom (incl. `sorryAx`, native_decide aux axioms), `implemented_by`/`extern`/`unsafe`/`partial`/`opaque` in the non-core closure, a theorem statement not mentioning a subject, lifted file ≠ re-lift of pinned wasm, kernel replay rejection (`leanexport` → `lake check --from-export`; `--paranoid` adds every bundled kernel). `lake build` success alone proves nothing (accepts sorry, axioms, kernel bypass).
- Prototype stack = Python via uv + Lean 4.35 core, no Mathlib.
- Prototype scope = trust audit + one worked example; repo survey/plan, claimcheck-style informalization, MCP/skill packaging, other link paths = later phases.

## Tasks

- [x] da4117c Lean package: WASM subset semantics (i32/i64, locals, select, block/loop/if/br/br_if/return, fuel interpreter, `Returns`)
- [x] da4117c Python lifter: wasm binary → Lean `Module` value + sha256 pin
- [x] da4117c Toy example: clamp/gcd/sum_to C → wasm → spec + proofs
- [x] bbc7825 Trust metaprogram + `fva trust` report (text + JSON)
- [x] bbc7825 Differential test vs wasmtime + `fva demo`; cheat example (red path)
- [ ] Kernel replay in `fva trust` (cheat 6: kernel-bypass `addDecl`)
- [ ] Review (closing diff), deferred rows, rules, Phase → ITERATE
- See `.agent/deferred.md` for the deferral queue.

## Phase

PROTOTYPE — whole product
