# isqrt

A library function that computes the integer square root of a 32-bit unsigned integer.

## Requirements

- R1: For every 32-bit unsigned input `n`, `isqrt(n)` returns the largest `r` such that `r * r <= n` (computed without overflow).
- R2: `isqrt` terminates for every input.

## Build

The shipped artifact is a WebAssembly module:

```sh
clang --target=wasm32 -O2 -nostdlib -Wl,--no-entry -Wl,--strip-all -Wl,--export=isqrt -o isqrt.wasm isqrt.c
```
