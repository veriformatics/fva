#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 verification/extract.py --check
wasm-tools validate lz4-c.wasm
lake build
# Re-elaborate every theorem file even when Lake's compiled files are cached.
lake env lean Proofs/Results.lean
lake env lean Proofs/Examples.lean
lake env lean Proofs/Format.lean
lake env lean Proofs/Audit.lean
test "$(wasmtime -C cache=n --preload artifact=lz4-c.wasm --invoke check verification/smoke.wat)" = 1
echo 'PASS: Wasmtime checks of the unmodified module'
verification_tmp=$(mktemp -d)
trap 'rm -rf "$verification_tmp"' EXIT
python3 verification/instrument.py "$verification_tmp/instrumented.wasm"
wasm-tools validate "$verification_tmp/instrumented.wasm"
node verification/test.mjs "$verification_tmp/instrumented.wasm"
echo 'PASS: all partial-verification checks (full R1–R3 remain unproved)'
