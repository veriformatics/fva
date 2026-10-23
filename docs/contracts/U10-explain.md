# U10 contract — `fva explain` (tier: shallow, advisory)

Purpose: the prototype Decision "Non-expert review aid" rebuilt Lean-native (Decisions: Stack, Non-expert review aid). Advisory: the verdict stays with `fva trust`; a wrong explanation misleads a reader but never changes a verdict, and the examples' values never come from the model.

## Behavior (from the Decisions entry)
- X1 Proof status per claim = issues of a fresh `fva trust --json` naming the claim or its proofs (whole-name match) + the project-wide ones naming no claim; never saved.
- X2 Pass 1 (`codex app-server`, ephemeral read-only thread, `outputSchema`) explains each claim from the comment-stripped review-surface source + its elaborated statement + FVA's claim vocabulary (`FVA/Spec/CAbi.lean`, `FVA/Spec/Claims.lean`); pass 2 compares the explanation + computed examples with the intent (docstring, else the name) → `matches|weaker|stronger|different|vacuous`.
- X3 Examples for claims `∀ (x : BitVec n)…, Returns m "f" args res` about one lifted subject: inputs = pass 1's proposals + `0`, `1` per argument (mod 2^bits, deduplicated, at most 8); spec value = Lean's evaluation of `res` (`FVA.Explain.run` under `lake env lean`, 10 s per case, a killed case shown as too costly); binary value = `wasmtime run --invoke` on the subject's `.wasm` (signed arguments, results mod 2^bits, a trap shown). Other shapes print their elaborated statement.
- X4 Saved beside the spec module (`fva-explain.json`: model text + examples + verdicts + `inputsSha` + generation time); a rerun shows it without a model call, `--force` regenerates. `inputsSha` = model, effort, prompts, schemas, fixed inputs + caps, review-surface files, the subjects' `Lifted.lean` (numeral = `.wasm` bytes), the vocabulary files, `FVA/Explain.lean`; a mismatch or another claim set → STALE banner.
- X5 rc 0 = trust PASS ∧ text current ∧ every intent check `matches`; 1 otherwise; 2 usage/setup. `--json` = the same result as JSON.

## Evidence (E)
- E1 `scripts/test-trust` runs `fva explain` on the three examples (saved text, no model call; it runs `fva trust` itself): rc 0 each.
- E2 `FVATest.Explain` guards: staleness, proof-status matching (whole names), report text helpers, comment stripping (shared lexer with the D11 line counter).
- E3 Generated once with the model: every example claim `matches`; spec and binary values agree on every computed case.

## Status
- Built on `wt/u9`: `FVA/Tool/Codex.lean` (JSON-RPC client; a timer task kills a silent server and ends within 100 ms of a cancel, since the process waits for its tasks), `FVA/Explain.lean` (in-project helper), `FVA/Tool/Explain.lean` (CLI), `FVA.Trust.commentMask` shared by `codeLines` + `stripComments`.
- Deferred rows unchanged: D5 (blinding), D15 (verdict stability runs), D16 (kernel-confirmed example values), D17 (in-Lean case budget), D18 (relational claims' examples).
