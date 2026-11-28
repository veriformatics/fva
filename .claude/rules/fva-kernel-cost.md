---
paths:
  - "FVA/Impl/Decode/**"
  - "FVA/Impl/Exec/**"
  - "FVA/Lifted.lean"
  - "FVA/Tool/Lift.lean"
---

# Kernel evaluation cost (code the kernel runs: decoder, stepper, machine, lift)

- Lean's kernel keeps every term it reduces for the whole declaration (whnf + defeq caches): a call costs about its callee's instantiated body, copied at each call and retained; a byte read by `Nat.shiftRight v 8` on one numeral retains each shifted remainder (quadratic in the numeral's bytes). Measured (U28a contract E4, `docs/contracts/U28a-profile.md`): a 256-leaf `bif` body ≈ 70 KB + 0.75 ms per call; the decoder ≈ 50–85 KB + 0.5–0.8 ms per decoded instruction, mostly loop machinery (a small-body dispatch rewrite gained ≈ 18 %); a 64 KB byte walk on one numeral ≈ 2.1 GB.
- Consequences: read bytes inside `sub` windows, never byte by byte across a large numeral; keep per-step function bodies small; a computation's memory = its declaration's, so split a large kernel computation into many declarations (chunked `decode_eq`, segmented machine runs) instead of tuning one.
- Chunked `decode_eq` (U29c, `docs/contracts/U29c-bustools.md`): `fva lift` assembles `decode_eq` from chunks once the code section's content passes `Chunking.threshold` = 128 KiB (chunks of whole entries ≤ `target` = 32 KiB; frozen by measurement: a monolithic `decode_eq` on bustools' 455 KB code section died at a 16 GiB cap, 15 chunks elaborate in ≈ 190 s / 6.8 GB; a smaller target changes nothing for lean4lean, which declines on its heartbeat limit either way). Big numerals meet every kernel, not only Lean's: pack with shifts (`hi <<< (8 * m)`, bounds as `lo >>> (8 * m) = 0`), never `256 ^ m * hi` — con-ron's memory for a product grows with the product of the operand sizes (one 30 KB numeral × `256 ^ 29852`: 642 MB; bustools' packed code section: past 25 GB), a shift's with its result. Lean prints and reads numerals in decimal in time quadratic in their size (64 KB 7 s, 160 KB 40 s, 627 KB ≈ 10 min): code generation (a chunked module's numerals, `bytes` included, are `noncomputable`; monolithic lifts keep a compiled `bytes`, D106), `leanexport` (every `fva trust` run exports `bytes`, D107) and the Lean-based kernels' parse (con-leche ≈ 158 s on bustools). `scripts/test-lift-chunks` pins the chunked shapes under test policies.
- Measure before and after an edit on a hot path: `lake env lean` on a generated file with `/usr/bin/time -f '%e s %M KB'` under `systemd-run --user --scope -p MemoryMax=…`; elaboration-only (statement replaced by `example : True := trivial`) vs full separates elaboration from the kernel.
