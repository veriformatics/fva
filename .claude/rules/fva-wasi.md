---
paths:
  - "FVA/Spec/Wasi/**"
  - "FVA/Proof/Wasi/**"
  - "FVATest/Wasi/**"
  - "scripts/test-wasi"
  - "scripts/wasi-vectors.lean"
  - "scripts/wasi-imports.lean"
---

# WASI preview1 model (U29a, `docs/contracts/U29a-wasi.md`)

- Three layers, never conflated: W = `world m mem` (the WITX envelope under two named host
  assumptions — field-only struct writes, failures without effect — with labeled
  over-approximations: any errno without effect, blocking, any typed outcome outside the profile;
  and named pinnings of wasmtime's policy where WITX is silent: the contract's W list);
  `E` = the virtual host claims assume (wasmtime 50.0.0's policy where it lies in W, named
  completions elsewhere: the contract's departures list, mirrored in the README from U29b on);
  `fva run` vs `wasmtime run` (U29b) = evidence on a tested domain, never a theorem.
- Every behavior change to `FVA/Spec/Wasi/**` lands with: its source (WITX line, wasmtime `p1:` line
  or a pinned-wasmtime probe) in the docstring; a source-traced example in
  `FVA/Proof/Wasi/Examples.lean` (expected values from the source, never from running `exec`); the
  blind corpus case (`FVATest/Wasi/oracle/cases.jq` → `FVATest/Wasi/oracle/make` regenerates the
  vectors + probes; `make --check` gates them; `replay` checks them on the pinned wasmtime); T7
  (`FVA/Proof/Wasi/WfRun.lean`) kept proven. An `E` choice that departs from wasmtime = a contract
  departures-list entry + its `basis: contract` vectors.
- `scripts/wasi-vectors.lean` + `scripts/wasi-imports.lean` live outside `FVATest/`: every `.lean`
  under `FVATest/` enters the mutation module graph (`.claude/rules/fva-mutation.md`), whose
  modules need oleans; the scripts run interpreted (`lake env lean --run`, ≈ 40 s for 164 vectors).
- Gate step `wasi` (`scripts/test-wasi`: the vectors, the model's numbering vs the WITX table
  `FVATest/Wasi/oracle/abi.tsv` + the import link check on wasmtime; full gate `--oracle` adds the
  ≈ 75 s wasmtime replay) = mutation stage `test:wasi` (helpers): a model defect must exit 1 (a
  call name the model lacks included), never 2 (fvamut records no row for a stage's rc 2).
  Corpus rows 183+ = MAIN's kills of the mutants rows 1–182 leave alive (README `Rows 183+`): a
  survivor of `test:wasi` → a row in that range (wasmtime basis wherever the pinned wasmtime
  decides: `replay` checks it), else a ruling. A mutant whose vector run exhausts the stage's
  memory or time before a vector fails (fvamut `inconclusive … crash: memory over` |
  `inconclusive test:wasi timeout`: rows 194 + 196's result pointer 65,524 read as an iovec
  count = 65,524 in-bounds regions, then the pairwise apartness check over them, > 120 s per
  vector; the runner reads every vector) → a kernel `decide` pin in `FVA/Proof/Pin/Wasi.lean`
  (`proofs` runs before `test:wasi`; a pin added to `Examples.lean` instead re-keys every row that
  module kills).
  Seen firing: tester-5's `fd_write.zero-past-eof` red on 7f9a6bd (a 0-byte write past EOF
  zero-filled the gap; wasmtime leaves the file) → fixed; reviewer-5's 13 boundary vectors (rows
  166–182: memory end, directory + sync fdflags, the `off_t` limit, a removed directory) red on
  27389b8 → fixed; MAIN's rows 228 + 235 (a final `..` above the dirfd: wasmtime `perm`) red on
  b6876d4 (unlink `isdir`, rmdir `inval`) → fixed; test-checks plants (a vector's errno changed, a
  call name the model lacks, a WITX table value changed → rc 1, a malformed vector → rc 2; a
  neutered harness returns 0 on the changed one).
- A model bug that lets a write near 2^63 succeed builds a huge file: its vector or example never
  ends instead of going red ⇒ run red checks of such cases under `systemd-run --user --scope -p
  MemoryMax=8G`; size examples take a symbolic length (`simp` expands a literal
  `List.replicate (2 ^ 63) …`).
- `fva run` (U29b2, `FVA/Tool/Run.lean` = glue graded by `scripts/test-wasi-run`): machine segments
  end at each host call, `answerHost (wasiHost …)` answers it and its stdout/stderr bytes are
  emitted at once (stream order kept); `random_get` = fresh bytes or `--random`'s; every stop syncs
  the trees back first; one `fva run: ` diagnostic at most, after the guest's last stderr byte.
  Its states = `sysRun`'s (`sysRunRem_eq`); `--fuel` counts steps exactly (`sysRunRem_spent`). A
  behavior change lands with a corpus case (`FVATest/Wasi/run/cases.jq` → `make`; expected bytes
  from the contract or the pinned wasmtime, never from running `fva`) + its testsuite comparison.
