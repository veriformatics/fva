#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 verification/extract.py --check
python3 verification/gen_cases.py --check
wasm-tools validate lz4-flex.wasm
lake build
lake env lean verification/Audit.lean
lake env lean --run Proofs/Corpus.lean
python3 verification/wasmtime_cases.py
node verification/test.mjs
echo 'PASS: all documented checks (the universal R1-R3 obligations remain open)'
