---
paths:
  - "lean-toolchain"
  - "lakefile.toml"
  - "lake-manifest.json"
  - "renovate.json"
  - "Main.lean"
  - "FVATest/*.lean"
  - "scripts/check-pins"
  - "scripts/fetch-tools"
---

# Lake package law

- Pins move together: `lean-toolchain` = installed `lean` = Mathlib tag in `lakefile.toml` = `lake-manifest.json` inputRev (`scripts/check-pins`); Renovate groups Lean + Mathlib and never automerges. Tool binaries (scanners, shellcheck, shfmt, wasm-tools, wasmtime) = `scripts/fetch-tools` (version + sha256; a Renovate bump fails there until the sha256 is refreshed from the release), so CI + every host check with one version: `scripts/` disables shellcheck codes by number, and SC2329 exists from 0.11.0 on (an older shellcheck reports SC2317 there instead).
- `FVATest` and the `fva` executable (`Main.lean`) import the executable modules they run (spec, impl, tools), never the proof modules: a planted impl bug then still builds the tests and `fva difftest`, which must catch it on their own (the U12 mutation check relies on this).
