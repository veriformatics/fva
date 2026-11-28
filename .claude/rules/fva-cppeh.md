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
  `FVA/Proof/**` module (a planted machine bug must reach the run, never a proof first). The
  proofs run on U29b's executable host (`wasiHost`, `Links`); `Run` keeps its stub.
- `Spec.lean` = `r1` (U28g, `docs/contracts/U28g-cpp-claim.md`; surface 13 lines): from one fixed
  process start, every launch of `eh` on any `x : BitVec 32` returns exactly `x + 1` (even) or
  `x ^^^ 0xa5a5a5a5` (odd) under the WASI model restricted to `E`, fitting growth. Proof = F1
  framing (`FVA/Proof/Exec/Oblivious*.lean`: a `trun`-certified segment keeps `SysMust` for every
  `x`) + F2 seams (`Seams`, `Links`: symbolic steps between segments) + F3 composition (`Core` over
  abstract cut states, `Proof`). `Twin` = the kernel facts at each cut (20 `kernel_rfl`
  declarations: 10 `trun` certificates (6 odd, 4 even), `instF` + 9 cut bundles, each re-running
  its twin prefix from launch; ≈ 450 s, 4.8 GB): the cut indices = the twins' (x = 1 odd, x = 0
  even) transition counts at the seams, so a change to `eh.wasm`'s decoded module fails `Twin` at
  the kernel (custom-section contents never reach it: byte identity = the placed file's sha256
  pin + the rebuild `cmp`); re-derive the cuts from a step-by-step `Machine` trace of both twins
  (code head + stack per transition), then the seams. `Proof` also holds `start_wf` and
  `eh_path` (path evidence: every launch's final store holds exactly one exception instance on an
  odd input, none on an even one), outside `r1` and the replay export (`fva trust` exports the
  claims' proofs + witnesses): Lean's kernel checks both when test-subjects builds the root.
- Gate law + firings: `.claude/rules/fva-checks.md` (test-subjects' CppEH part; the C++ EH subject
  build + fingerprint entry).
