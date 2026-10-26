#!/usr/bin/env bash
# Run from the Lake project root. Every failing check aborts this script.
set -euo pipefail
sha256sum -c verification/inputs.sha256
wasm-tools validate edgeR.so
frama-c --check-wp . verification/counterexamples.c \
  -wp -wp-model Typed+float -wp-prover alt-ergo -wp-timeout 10 \
  -wp-rte -wp-cache none 2>&1 | tee verification/wp.log
node verification/artifact.cjs | tee verification/artifact.log
Rscript verification/filter.R 2>&1 | tee verification/filter.log
printf '%s\n' 'All verification checks passed (both requirements have counterexamples).'
