#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")/.."
python3 verification/lift.py
frama-c --check-wp . verification/base.c -machdep x86_32 \
  -wp -wp-rte -wp-split -wp-timeout 10 -wp-par 4 -wp-prover qed,alt-ergo
python3 verification/instrument.py
node verification/test.js
