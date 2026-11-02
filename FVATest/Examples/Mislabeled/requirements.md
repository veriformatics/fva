Requirements for the exported functions of mislabeled.wasm, a C library compiled to
WebAssembly. Integers are 32-bit and signed.

## R1
clamp(x, lo, hi) returns lo when x < lo, hi when x > hi, and x otherwise (for lo <= hi).
