Implemented Lean 4 proofs of R1 correctness and R2 termination for the exact shipped WebAssembly.

Checks passed: `lake build`, six-kernel replay, byte-identical rebuild/re-lift, and 200 FVA differential cases.

`fva trust` cannot run its nested sandbox here; separate kernel replay succeeds without that layer.

See [VERIFICATION.md](/tmp/fva-bench/fva-isqrt/prototype/fva/examples/isqrt/VERIFICATION.md) for commands, proof connections, and trust limits.