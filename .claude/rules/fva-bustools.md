---
paths:
  - "FVATest/Subjects/Bustools/**"
---

# bustools subject (D28, `docs/contracts/U29c-bustools.md`)

- `bustools-count.wasm` = `build`'s output alone: bustools `d4d7a283` `src/` (each file
  sha256-pinned, cached in `.cache/bench/bustools-d4d7a283`), `stubs.cpp` (the 17 aborting entry
  points of the other commands), the pinned wasi-sdk 34.0, one staging dir compiled under
  `-ffile-prefix-map=<stage>=/bustools` (an `assert`'s `__FILE__` lands in the data section: a
  host path would make the bytes host-dependent and personal), the pinned link order + output
  basename (wasm-ld writes the basename into the name section). Never committed (Decisions:
  Repository contents): published on veriformatics/fva-artifacts (`subject-builds-v2`:
  `NOTICE-bustools-count.txt` + `license-*.txt`), placed by `scripts/fetch-subjects`
  (`bench/subjects/manifest.json` `builds` `bustools-count-wasm`); test-subjects' Bustools block
  rebuilds it + `cmp`s the placed bytes. A change to `build`, `stubs.cpp`, a source pin or the SDK
  → rebuild, then in the same commit: a new release (released files never change), the manifest
  entry's `url` + sha256, `build`'s expected sha256, `fingerprint`'s counts.
- `Lifted.lean` = test-subjects' lift loop output (gitignored): its code section exceeds `fva
  lift`'s chunking threshold, so `decode_eq` is assembled from chunks (`FVA/Tool/Lift.lean`
  `Chunking`, `.claude/rules/fva-kernel-cost.md`).
- `preflight [WASM]` (C4) = concrete-run evidence: upstream tc0004 (`fromtext -p … | count … -`,
  two fresh processes) by `fva run` and the pinned wasmtime, every exit status, stream and output
  file equal, `output.mtx` = upstream's under `diff -w -B`; the inputs are sha256-pinned in the
  script. Seen firing: `MatrixMarket` → `matrixMarket` in the wasm's data → rc 1 (`output.mtx
  differs from upstream's`; both engines agree on the planted output). D28's claim (`SysMust` under `E`, every `random_get` value) = U29f; `Spec.lean`'s
  `wasiImports` = U29c's link-only test claim, replaced there.
- `fva trust` on this subject ≈ 25 min per mode (10 of them exporting `bytes`, D107) ⇒ the schedule
  runs it (Decisions D28 gate placement; U29d's workflow): `FVA_SUBJECT_SCHEDULED=1
  scripts/test-subjects --shard K/N` adds its row (surface 10); per commit its root builds alone.
- Gate law + firings: `.claude/rules/fva-checks.md` (test-subjects' Bustools part).
