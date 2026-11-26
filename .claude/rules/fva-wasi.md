---
paths:
  - "FVA/Spec/Wasi/**"
  - "FVA/Proof/Wasi/**"
  - "FVATest/Wasi/**"
  - "scripts/test-wasi"
  - "scripts/wasi-vectors.lean"
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
- `scripts/wasi-vectors.lean` lives outside `FVATest/`: every `.lean` under `FVATest/` enters the
  mutation module graph (`.claude/rules/fva-mutation.md`), whose modules need oleans; the script
  runs interpreted (`lake env lean --run`, ≈ 40 s for 164 vectors).
- Gate step `wasi` (`scripts/test-wasi`; full gate `--oracle` adds the ≈ 75 s wasmtime replay).
  Seen firing: tester-5's `fd_write.zero-past-eof` red on 7f9a6bd (a 0-byte write past EOF
  zero-filled the gap; wasmtime leaves the file) → fixed; reviewer-5's 13 boundary vectors (rows
  166–182: memory end, directory + sync fdflags, the `off_t` limit, a removed directory) red on
  27389b8 → fixed; test-checks plants (a vector's errno changed → rc 1, a malformed vector → rc 2;
  a neutered harness returns 0 on the changed one).
- A model bug that lets a write near 2^63 succeed builds a huge file: its vector or example never
  ends instead of going red ⇒ run red checks of such cases under `systemd-run --user --scope -p
  MemoryMax=8G`; size examples take a symbolic length (`simp` expands a literal
  `List.replicate (2 ^ 63) …`).
