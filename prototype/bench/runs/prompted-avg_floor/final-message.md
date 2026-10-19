R1 and R2 are **false**: two `INT_MAX` inputs return `-1`.

Added artifact-linked Lean proofs of the exact correctness boundary and counterexamples. The C source is unchanged.

`./verify.sh` passed all three kernels, false-proof rejection controls, and artifact-binding checks.

[VERIFICATION.md](/tmp/fva-bench/prompted-avg_floor/VERIFICATION.md) documents the commands, limitations, and review sizes: 74 project-specific lines and 515 transitive dependency constants.