#!/usr/bin/env bash
# How glm-iround.wasm was built (WASI SDK 34.0 clang 23.1.0; not needed to verify the artifact).
set -euo pipefail
clang++ --target=wasm32-wasip1 -mcpu=generic -mno-simd128 -mno-relaxed-simd -std=c++17 \
	-DNDEBUG -O2 -fno-exceptions -nostdlib -I. \
	-Wl,--no-entry -Wl,--strip-all -Wl,--export=iround iround.cpp -o glm-iround.wasm
