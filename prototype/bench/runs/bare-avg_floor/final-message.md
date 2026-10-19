Added machine-checked Lean 4 proofs and [VERIFICATION.md](/tmp/fva-bench/bare-avg_floor/VERIFICATION.md).

**R1 and R2 are false:** the shipped Wasm returns `-1` for `(INT_MAX, INT_MAX)`, instead of `INT_MAX`.

The proofs establish exact all-input behavior and correctness **iff the mathematical sum fits signed 32 bits**, tied to the artifact’s exact bytes.

Clean build, file-identity checks, and axiom audit passed offline. Original code and Wasm remain unchanged.