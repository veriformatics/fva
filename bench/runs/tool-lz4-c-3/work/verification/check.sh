#!/usr/bin/env bash
# Run from the repository root. Any failed theorem/test stops this script.
set -euo pipefail
unset PYTHONOPTIMIZE
sha256sum --check verification/inputs.sha256
python3 verification/prepare.py
mkdir -p verification/results
frama-c --check-wp . verification/memory.c -machdep x86_32 \
  -wp -wp-model Bytes -wp-rte -wp-prover alt-ergo -wp-timeout 60 -wp-cache none \
  2>&1 | tee verification/results/memory.log
frama-c --check-wp . verification/entry.c -machdep x86_32 \
  -inline-calls LZ4_decompress_safe \
  -wp -wp-fct entry_read,LZ4_decompress_generic,verify_zero_capacity,verify_empty_source \
  -wp-model Bytes -wp-rte -wp-prover alt-ergo -wp-timeout 15 -wp-cache none \
  2>&1 | tee verification/results/entry.log
python3 verification/artifact.py | tee verification/results/artifact.log
node verification/runtime.mjs | tee verification/results/runtime.log
printf '%s\n' 'All stated partial results checked. General R1/R2/R3 remain unproved.'
