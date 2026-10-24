# Integer rounding in GLM (WebAssembly build)

`glm-iround.wasm` is the WebAssembly build (66 bytes, sha256 `eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a`) of GLM 1.0.3's `glm::iround` for `double`, from the unmodified headers in `glm/` (OpenGL Mathematics, a C++ mathematics library). `iround.cpp` exports the function, and `build.sh` records how the module was built (a release build). The module is the artifact to verify.

## Interface

The module exports `iround(x)`: `x` is an `f64` value and the result is an `i32` value. `glm/ext/scalar_common.hpp` documents the function: "Returns a value equal to the nearest integer to x." and "The values of the argument must be greater or equal to zero."

## Requirements

- R1: For every finite `x` with `0 ≤ x ≤ 2147483647`, `iround(x)` returns the integer nearest to `x`. When `x` lies exactly halfway between two integers, either of them is accepted.
