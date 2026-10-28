#!/usr/bin/env bash
# Run from the project root. Every unsuccessful proof/test makes this fail.
set -euo pipefail
python3 verification/prepare_wp.py
frama-c --check-wp . verification/memory-annotated.c \
  -machdep gcc_x86_32 -wp -wp-model Bytes -wp-rte \
  -wp-prover alt-ergo -wp-timeout 30 -wp-cache none \
  2>&1 | tee verification/memory.log
frama-c --check-wp . verification/decoder_wp.c \
  -machdep gcc_x86_32 -cpp-extra-args=-I./src \
  -wp -wp-model Bytes -wp-fct LZ4_decompress_generic,LZ4_decompress_safe \
  -wp-rte -wp-prover alt-ergo -wp-timeout 10 -wp-cache none \
  2>&1 | tee verification/decoder.log
frama-c --check-wp . verification/literals_model.c \
  -machdep gcc_x86_32 -wp -wp-rte -wp-split \
  -wp-prover alt-ergo -wp-timeout 10 -wp-cache none \
  2>&1 | tee verification/literals.log
python3 verification/check_artifact.py 2>&1 | tee verification/artifact.log
