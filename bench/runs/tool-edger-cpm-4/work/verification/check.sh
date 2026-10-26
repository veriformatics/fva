#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")/.."
python3 verification/build_witness.py 2>&1 | tee verification/artifact.log
Rscript --vanilla verification/check_r.R 2>&1 | tee verification/r.log
frama-c --check-wp . verification/requirements.c \
  -wp -wp-rte -wp-model Typed+float -wp-prover alt-ergo \
  -wp-timeout 10 -wp-cache none \
  2>&1 | tee verification/wp.log
printf '%s\n' 'PASS: all artifact assertions, R witnesses, and WP goals checked'
