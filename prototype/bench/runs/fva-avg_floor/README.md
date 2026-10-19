# avg_floor

A library function that averages two 32-bit signed integers.

## Requirements

- R1: For all 32-bit signed `a` and `b`, `avg_floor(a, b)` returns the mathematical floor of `(a + b) / 2`.
- R2: The result is correct for every input, including inputs whose sum does not fit in 32 bits.

## Build

The shipped artifact is a WebAssembly module:

```sh
clang --target=wasm32 -O2 -nostdlib -Wl,--no-entry -Wl,--strip-all -Wl,--export=avg_floor -o avg_floor.wasm avg_floor.c
```
