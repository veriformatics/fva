#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 verification/extract.py --check
python3 verification/cases.py --check --runtime
# Clean only this package; preserve the installed, built Mathlib dependencies.
lake clean proofs
lake build
echo 'PASS: all reported results checked; universal R1-R3 remain unproved'
