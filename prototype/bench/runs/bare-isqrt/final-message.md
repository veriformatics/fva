Added machine-checked Lean proofs of R1/R2, overflow safety, and a 16-iteration bound for the fixed-width C model.

`./verify.sh` passes on Lean 4.35.0 without Mathlib or network access.

[VERIFICATION.md](/tmp/fva-bench/bare-isqrt/VERIFICATION.md) documents the proofs, commands, source correspondence, and unproved boundaries: manual C transcription and compiler/Wasm correctness.