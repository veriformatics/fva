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
- Measure before and after an edit on a hot path: `lake env lean` on a generated file with `/usr/bin/time -f '%e s %M KB'` under `systemd-run --user --scope -p MemoryMax=…`; elaboration-only (statement replaced by `example : True := trivial`) vs full separates elaboration from the kernel.
