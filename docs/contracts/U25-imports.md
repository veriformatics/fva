# U25 contract — runner import matching + binary malformed checks (tier: kernel matcher, data runner)

Purpose: the official-script runner gives false greens on link-error and binary-malformed assertions: `assert_unlinkable` passes on validation alone (consultant-1 reproduced a planted false one passing while wasmtime fails it) and every `assert_malformed` is skipped (708 binary + 640 text in the pinned corpus). Decisions: Language + Wasm reach, "Runner import matching". Consumers: `scripts/test-spec`, U28e (tag import typing), the acceptance suite.

## Interface
- `FVA/Impl/Exec/Imports.lean` (verified): `Limits.matches`, `ExternVal.matches`, `Ref.importsMatch : Store → Module → List ExternVal → Bool`.
- `FVA/Proof/Exec/Imports.lean`: `importsMatch_iff : Ref.importsMatch s m imports = true ↔ ImportsMatch s m imports` (the reviewed relation in `FVA/Spec/Exec/Instantiate.lean`).
- Runner (`FVATest/Spec.lean`): import resolution = `linked` imports | `unknown` (a module name not registered or an export missing: a link error) | `unavailable` (a dependency FVA rejected: skip).

## Runner predicates
- `module`, `assert_uninstantiable`: resolved imports must match (`importsMatch`), else FAIL `imports do not match`; `unknown` ⇒ FAIL; `unavailable` ⇒ skip (as today).
- `assert_unlinkable`: payload validates (as today), then pass iff `unknown` or `importsMatch = false`; a module that links ⇒ FAIL `module links`; `unavailable` ⇒ skip.
- `assert_malformed`, binary payload: FVA's decoder `malformed` ⇒ pass; `unsupported` ⇒ outside (skip, counted); decoded + validator rejects ⇒ outside "rejected only by validation" (Wasm 3.0 classifies memarg flags ≥ 0x80 as malformed, 2.0 as invalid: `align.wast:968,987`; U28a adopts the 3.0 rule); decoded + valid ⇒ FAIL. Text payload ⇒ skip "text format" (FVA has no text parser; wasm-tools' parser is not under test).

## Evidence
- E1 pinned corpus counts updated in `scripts/test-spec` (binary malformed payloads become passes where FVA's decoder rejects them; unlinkable counts unchanged in total, now checked by matching). `scripts/test-decoder` already pins 702 malformed rejections over the binary-format scripts; the runner check extends the same decoder check to every script's malformed commands (align, global, EH, P' scripts) so a script's pass count is never inflated by skipped assertions.
- E2 planted (`scripts/test-checks`): a false `assert_unlinkable` (exact-match import) ⇒ runner rc 1; a false binary `assert_malformed` (well-formed module) ⇒ rc 1; each true counterpart ⇒ rc 0.
- E3 mutation: `FVA/Impl/Exec/Imports.lean` enters the `fvamut` scope; survivors ruled before the commit.
