#!/usr/bin/env bash
# Check completed results. General R1/R2/R3 proofs are not claimed.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 verification/artifact.py
python3 verification/check_prefix.py
python3 verification/prepare.py
frama-c --check-wp . verification/prefix.c -machdep x86_32 \
  -wp -wp-cache none -wp-rte -wp-timeout 10 -wp-par 8
frama-c --check-wp . verification/boundaries.c -cpp-extra-args=-Isrc \
  -machdep x86_32 -inline-calls LZ4_decompress_safe,LZ4_decompress_generic \
  -wp -wp-cache none -wp-model Bytes -wp-fct empty_source,zero_capacity \
  -wp-rte -wp-timeout 10 -wp-par 8
frama-c --check-wp . verification/memory.annotated.c -cpp-extra-args=-Isrc \
  -machdep x86_32 -wp -wp-cache none -wp-model Bytes -wp-fct memmove \
  -wp-rte -wp-timeout 10 -wp-par 8
python3 verification/replay.py
printf '%s\n' 'Completed checks passed. General R1, R2 and R3 remain unproved.'
