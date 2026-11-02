---
paths:
  - "FVA/Trust/**"
  - "FVA/Spec/Trust.lean"
  - "FVA/Proof/Trust.lean"
  - "FVA/Tool/Trust.lean"
  - "FVA/Tool/Sandbox.lean"
  - "FVA/Self/**"
  - "FVATest/Trust.lean"
  - "FVATest/Cheats/**"
  - "trust/**"
---

# `fva trust` law (U7, `docs/contracts/U7-trust.md`)

- Claims = the spec module's `@[fva_claim]` definitions (`FVA/Spec/ClaimAttr.lean`, imported by every lifted and blob module through `FVA.Lifted`) + any theorem there (`[layout]`); the tag is read from `.olean` entries (`TagAttribute.hasTag` works under `loadExts := false`, scoped extensions such as instances do not); unmarked `Prop` defs = `Report.unmarked`, listed, never a FAIL.
- Verdict = `FVA.Trust.verdict` over a `Report`, proven `= .pass ↔ Pass r` (`FVA/Proof/Trust.lean`); `FVA/Spec/Trust.lean` = the reviewed-once rules, imports nothing (it enters every project's closure). A new rule = a `Pass` conjunct + a `rule*` function + its `_nil` lemma + a cheat that fires it.
- Project code (Lake config, build, `lake env`, explain's `lake env lean`) + the exporter run in `FVA.Tool.Sandbox` (bwrap: `/` ro, home covered ro, no network, writable = `.lake` dirs + the caller's temp dir); a new process that runs project code goes through it too, since an unsandboxed one hands the project the user's account.
- Collection = trusted glue reading untrusted projects: imports run no project initializer (`loadExts := false`); no `git` or other process inside `.lake/packages/*` (repository config can run commands; a local mutation run integrity-checks that tree) — package pins come from `lake-manifest.json` + `.git/HEAD` read as files; the lifted `source` must stay inside the project; the export goes to a private temp dir.
- Origin by file, never by name: core = sysroot; Mathlib = packages pinned exactly as FVA's own manifest pins them, every such module's compiled files = `trust/oleans.tsv`'s pins (D48 `[olean]`); base = the FVA package's modules (in-package projects; consumer path = U11), their compiled files pinned the same way (D49); else project. `trust/oleans.tsv` = `scripts/make-olean-pins` output after `lake build` (every FVA edit changes base pins: regenerate with the build, like `BaseManifest.lean`) and after a Mathlib or dependency pin change, from a fresh `lake exe cache get`.
- Cheats = in-package projects `FVATest/Cheats/<Name>/{Spec,Proof,Lifted…}.lean` (no lakefile entry: `lakefile.toml` is in the U12 mutation manifest), each pinned in `scripts/test-trust` with its exact tag set; every `Lifted.lean` = `scripts/make-cheats` output (`fva lift` + each link cheat's planted edit), rerun after any `fva lift` format change since `fva trust` demands byte-identical re-lifts; `FVATest.Trust` + `FVATest.Explain` = glue checks imported by `FVATest.Main` (`lake test` runs them; their report-text guards kill the verdict module's wording mutants in the U12 `exes` stage). Cheats, examples + negative certificates stay outside the mutation graph (`config.json` `exclude`: the primary build never builds them).
- Canaries: `trust/canaries/set.tsv` (pinned names + sha256) ← `scripts/fetch-canaries --pin` after an arena or #15704 pin change; `known.tsv` = documented acceptances, each covered by another run-set kernel's reject; `matrix.tsv` ← `fva trust-matrix --canary-limit 120` (statuses only) after any toolchain or canary pin change, then re-justify the default run set (V3). Canary statuses cache per kernel binary + invocation (`Kernel.configId`) + canary sha256: a kernel flag change re-runs them.
