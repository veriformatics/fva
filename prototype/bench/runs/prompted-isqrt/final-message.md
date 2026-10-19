Implemented Lean 4 proofs of correctness and termination for the shipped Wasm, with a byte-identical rebuild from unchanged C.

```sh
./check.sh
```

Passed: three independent kernels, false-proof rejection, `sorry` rejection, and artifact-mutation detection.

Formal review surface: **109 lines / 4,027 bytes**.

[VERIFICATION.md](/tmp/fva-bench/prompted-isqrt/VERIFICATION.md) documents the proofs, implementation link, commands, and trust boundaries.