#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 verification/generate.py --check
wasm-tools validate lz4-flex.wasm
lake build
lake env lean Proofs/Results.lean
python3 verification/replay.py
echo 'PASS: all delivered checks; universal R1/R2/R3 remain unproved (see VERIFICATION.md)'
