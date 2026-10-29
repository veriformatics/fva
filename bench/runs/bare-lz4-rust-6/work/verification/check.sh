#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 -B verification/extract.py --check
wasm-tools validate lz4-flex.wasm
python3 -B verification/cases.py --check --wasmtime
lake build
lake env lean verification/Audit.lean
echo 'PASS: all delivered partial verification results checked'
