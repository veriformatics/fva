# sat_add

A library function that adds two 32-bit signed integers and saturates instead of wrapping.

## Requirements

- R1: For all 32-bit signed `a` and `b`, if the mathematical sum `a + b` is in the 32-bit signed range, `sat_add(a, b)` returns it.
- R2: If `a + b` is greater than 2147483647, `sat_add(a, b)` returns 2147483647.
- R3: If `a + b` is less than -2147483648, `sat_add(a, b)` returns -2147483648.

## Build

The shipped artifact is a WebAssembly module:

```sh
clang --target=wasm32 -O2 -nostdlib -Wl,--no-entry -Wl,--strip-all -Wl,--export=sat_add -o sat_add.wasm sat_add.c
```
