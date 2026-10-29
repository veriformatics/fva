#!/usr/bin/env bash
set -euo pipefail
# Run from the project root. All dependencies are local; no downloads or source rebuild.
python3 verification/extract.py --check
wasm-tools validate lz4-flex.wasm
lake build Proofs.Fixtures
lake env lean Proofs/Cases.lean
lake env lean verification/Export.lean
node verification/runtime.mjs
empty_result=$(wasmtime run -C cache=n --invoke lz4_decompress lz4-flex.wasm 131072 1048576 0 0)
zero_result=$(wasmtime run -C cache=n --invoke lz4_decompress lz4-flex.wasm 131072 1048576 1 0)
test "$empty_result" = '-1'
test "$zero_result" = '0'
printf '%s\n' 'PASS: Wasmtime empty-input and zero-token checks' 'PASS: all verification checks (scope and gaps in VERIFICATION.md)'
