## Intent

FVA (Formally Verify Anything) aims to follow a software development tooling trend brought on by REA (Reverse Engineer Anything): https://github.com/morluto/rea. Our goal is to allow a user to apply FVA to any pre-existing or new project and find a path towards formal verification of it. It is important that the formal verification is directly linked to the code of the software's actual implementation, for instance Verus is tightly integrated with Rust, and Lean allows for metaprogramming. For other languages, we may have to develop our own solutions and it is best if we can find a unified approach to avoid an excess of language-specific handling, which is likely to be brittle and inelegant in approach.

Like REA, FVA should be readibly usable by an AI agent that requests it, and that is the primary target. FVA uses extensive AI-generated proofs to achieve its verification claims. At the same time FVA should aim to minimize the surface of human-reviewable spec. This is treated as an optimization problem: provided a minimally sufficient spec, and a trusted kernel like that of Lean's, we can assume that an unbounded amount of proofs can be used to verify correctness of a program. See https://github.com/schildep/verified-3d-mesh-intersection, for an excellent example of this approach. Spec review may be further simplified by informalization back into natural language (https://github.com/metareflection/claimcheck); we must be open to considering alternative and supplementary approaches at all times.

## Artifacts

- `prototype/fva/` = PROTOTYPE: Python (uv) CLI `fva` + Lean 4.35 core package `prototype/fva/lean` (WASM semantics, proof support, `fva-trust` metaprogram) + worked examples `prototype/fva/examples/{toy,cheat}`; human entry = `prototype/fva/README.md`.
  - Run: `cd prototype/fva && uv run fva demo` = rebuild toy C → wasm vs pinned sha, difftest Lean semantics vs wasmtime, trust report `examples/toy` (PASS) + `examples/cheat` (FAIL); rc 0 = all as expected.
  - Subcommands: `uv run fva lift <wasm> <out.lean> --ns <Ns>`, `uv run fva trust <lake-dir> [theorem…] [--spec-module M] [--paranoid] [--json]`, `uv run fva difftest <lake-dir>`, `uv run fva explain <lake-dir> [--model M] [--effort E] [--json]`.
  - Review aid run: `cd prototype/fva && uv run fva explain examples/toy` (rc 0: trust PASS + every intent check `matches`) + `uv run fva explain examples/cheat` (rc 1: all 7 cheats ✗ on proof status, vacuous/different intent on clamp/sum_to*/gcd_terminates/sumBelow_ten); LLM output varies run to run.
  - Needs: uv, Lean 4.35 + lake (bundles `leanexport`, `lake check`, nanoda/con-leche/con-ron for `--paranoid`), clang wasm32 target; `fva explain` + signed-in `codex` CLI.

## Decisions

- Link path = WASM lift: any source language → wasm (compiler + source untrusted) → `fva lift` → Lean `Module` value over FVA's WASM semantics; theorems quantify over that value via `Returns`; the `.wasm` = the verified artifact, committed + sha256-pinned in the lifted file; `fva trust` re-lifts + byte-compares.
- Trusted base = Lean kernel + axioms {propext, Classical.choice, Quot.sound} + `FVA/Wasm/Semantics.lean` (shared across every project/language, reviewed once) + `src/fva/lift.py`; difftest vs wasmtime = evidence for semantics + lifter, not proof.
- Claims = `Prop`-valued defs in `<Lib>/Spec.lean`; proofs = theorems typed by the claim constant, downstream in `<Lib>/Proof.lean` (never read); `<Lib>/Lifted.lean` generated. Spec imports reviewed modules alone; reverse (mesh-repo) layout lets unreviewed macros/notation change spec meaning.
- Human-review surface = every module in the spec module's import closure minus Lean core, FVA base + subject, read whole (code lines counted); statement closure reports which subject/base/core names the claims use. Core/base = by `.olean` origin (Lean sysroot / FVA install), never by module name.
- `fva trust` FAIL on: unproven claim, non-standard axiom (incl. `sorryAx`, native_decide aux axioms), syntax extension in a review module, `implemented_by`/`extern`/`unsafe`/`partial`/`opaque` in the non-core closure, a claim not mentioning a subject, lifted file ≠ re-lift of pinned wasm, kernel replay rejection (`leanexport` → `lake check --from-export`; `--paranoid` adds every bundled kernel). `lake build` success alone proves nothing (accepts sorry, axioms, kernel bypass).
- Prototype stack = Python via uv + Lean 4.35 core, no Mathlib.
- Non-expert review aid = `fva explain`, layered under `fva trust` (verdict stays there; explain = advisory): per claim → proof status (trust issues naming it + project-wide ones), plain-English breakdown + caveats, examples table, intent check.
  - Method = Claimcheck's two-pass round trip, reimplemented (Claimcheck itself parses Dafny + calls Anthropic/Vertex/Bedrock only): pass 1 explains from comment-stripped spec source + each claim's elaborated statement (post-macro = what the kernel checks; source text alone hid cheat 7's `False →` on 3 claims); pass 2 = separate call comparing pass 1 with intent → `matches|weaker|stronger|different|vacuous`.
  - Intent = claim docstring, else its name. Blinding beyond docstring stripping (names, independent requirements) = out of scope for now (user ruling: this round tests LLM breakdown of a spec).
  - Example values never come from the model: inputs = model-proposed + fixed `0`,`1` per argument; spec value = Lean evaluation of the claim's `Returns` result (claims of shape `∀ (x : BitVec n)…, Returns m "f" args res`; other shapes print their elaborated statement instead); binary value = wasmtime on the pinned `.wasm`.
  - LLM backend = `gpt-6-luna` via `codex app-server` (JSON-RPC stdio, ephemeral read-only thread, `outputSchema`-constrained reply), both passes.
- Prototype scope = trust audit + one worked example + `fva explain`; repo survey/plan, MCP/skill packaging, other link paths = later phases.

## Tasks

- [x] b5d1ef2 Round 1: non-expert review of the spec → `fva explain` (Claimcheck-style round trip + computed examples + per-claim proof status).
- See `.agent/deferred.md` for the deferral queue.

## Phase

ITERATE — whole product
