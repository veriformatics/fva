#!/usr/bin/env bash
# Run from any directory. No network or source rebuild is needed.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 verification/generate.py --check
python3 verification/generate_cases.py --check
wasm-tools validate lz4-flex.wasm
verus --version
verus --no-cheating verification/machine.rs
wasmtime run -C cache=n --preload decoder=lz4-flex.wasm --invoke check verification/runtime.wat
