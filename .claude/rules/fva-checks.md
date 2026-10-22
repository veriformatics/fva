---
paths:
  - "scripts/**"
  - ".gitleaks.toml"
  - "renovate.json"
  - ".github/workflows/**"
---

# Gate check law

- Every gate step was seen failing on a planted input (U1): build (unused variable under `--wfail`), test (`#guard false`), lint (`unusedArguments` on a theorem), shellcheck (SC2086), shfmt (indent diff), spec-lint (malformed Tasks row), gitleaks (planted AWS key → 1 leak), osv-scanner (`requests==2.19.0` → 20 known vulnerabilities), actionlint (unexpected step key), zizmor (template-injection, rc 14), check-format + check-pins (via test-checks). A step added later ships with its planted-input firing recorded here.
- Purpose-built checks are proven on every run: a new case or check → add its planted inputs to `scripts/test-checks` (throwaway copies; never the working tree); a neutered check (forced `exit 0`) must make test-checks fail.
- `.gitleaks.toml` allowlists only gitignored paths (`.lake/`, `.tools/`, `.scratch/`, `.venv/`); without it `gitleaks dir` scans Mathlib + scratch (8.5 GB, 205 false hits).
- Workflows: actions pinned by commit SHA + version comment; `permissions: contents: read`; checkout with `persist-credentials: false`; CI runs `scripts/gate` unchanged after lean-action installs the toolchain + Mathlib cache.
