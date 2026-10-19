Added Lean 4 proofs of R1–R3 for the C model and decoded shipped Wasm, including overflow and cast safety.

`./verify.sh` passes, including the 21-theorem axiom audit. Original C/Wasm files are unchanged.

[VERIFICATION.md](/tmp/fva-bench/bare-sat_add/VERIFICATION.md) documents the proofs, checking commands, code correspondence, and remaining semantic-model assumptions.