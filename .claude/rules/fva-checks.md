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
- `.gitleaks.toml` allowlists only gitignored paths (`.lake/`, `.tools/`, `.scratch/`, `.cache/`, `.venv/`); without it `gitleaks dir` scans Mathlib + scratch (8.5 GB, 205 false hits).
- `scripts/test-decoder` (decoder E1/E2/E5 on the pinned corpus from `scripts/fetch-corpus` → `.cache/corpus`, sha256-checked; GPL binaries fetched, never committed) pins its counts (702 malformed, 186 valid, 188 round trips over the binary-format + numeric scripts), so an empty run fails. Seen firing on planted decoder bugs: overlong LEB accepted (u32 fuel 6 + N check off → E1 688/702), section-size check dropped (E1 695/702), i32.add/sub swapped (E2 55/58), export kinds func/table swapped (E2 53/58), data bytes + 1 (E2 57/58); E5 rejects `len` + 1 and one changed byte at the kernel. The N > 7 check alone is an equivalent mutant (fuel = ⌈N/7⌉ bounds the length the same way).
- `scripts/test-numerics` (U3 E1: official numeric scripts → `fvatest numeric`, straight-line exports evaluated against the reviewed numeric spec, others skipped) pins pass/fail/skip per script; update the table only with the change that moves it. Seen firing: `idiv_s` with Euclidean `/` in place of `Int.tdiv` → i64 379/5, int_exprs 87/2, i32 failures.
- Workflows: actions pinned by commit SHA + version comment; `permissions: contents: read`; checkout with `persist-credentials: false`; CI runs `scripts/gate` unchanged after lean-action installs the toolchain + Mathlib cache.
