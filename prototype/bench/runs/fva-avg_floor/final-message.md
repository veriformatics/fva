R1 and R2 are false: `avg_floor(INT_MAX, INT_MAX)` returns `-1`.

Added Lean proofs of exact binary behavior and both requirement refutations. All six kernels accepted; FVA differential testing passed. FVA’s normal replay hit a sandbox limitation, documented with the successful separate replay.

See [VERIFICATION.md](/tmp/fva-bench/fva-avg_floor/prototype/fva/examples/avg_floor/VERIFICATION.md) for proofs, code linkage, and exact checking commands.