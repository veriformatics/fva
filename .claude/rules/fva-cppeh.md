---
paths:
  - "FVATest/Subjects/CppEH/**"
---

# C++ EH subject (D29, `docs/contracts/U28f-cpp-subject.md`)

- `eh.wasm` = `build`'s output alone: the pinned wasi-sdk 34.0, then `fingerprint`. Never
  committed (Decisions: Repository contents): published on veriformatics/fva-artifacts
  (`subject-builds-v1`: `NOTICE-eh.txt` + `license-*.txt`), placed by `scripts/fetch-subjects`
  (`bench/subjects/manifest.json` `builds` `cpp-eh-wasm`: url + sha256); the full gate rebuilds it +
  `cmp`s the placed bytes (acceptance `D29.cpp-build`); `Lifted.lean` = test-subjects' lift loop
  output (gitignored). A change to `eh.cpp`, `build` or the SDK pin → rebuild, then in the same
  commit: a new fva-artifacts release with the bytes + notice (released files never change), the
  manifest entry's `url` + sha256, the counts in the README's Fingerprint section, `Run.lean`'s
  expectations where the host calls or exceptions per input move. Byte equality holds at the
  output basename `eh.wasm` alone: wasm-ld writes the output's basename into the name section.
- `Run.lean` = test-only evidence (the machine vs the source contract under a fail-closed stub
  WASI host): no claim, spec or proof module imports it, and its own import closure holds no
  `FVA/Proof/**` module (a planted machine bug must reach the run, never a proof first). U29b's
  executable host replaces the stub.
- `Spec.lean` = tester-1's non-binding `Returns` draft, false for this artifact (7 WASI imports, the
  throw path calls `environ_sizes_get`); U28g replaces it with the system claim under the WASI
  model + `E`.
- Gate law + firings: `.claude/rules/fva-checks.md` (test-subjects' CppEH part; the C++ EH subject
  build + fingerprint entry).
