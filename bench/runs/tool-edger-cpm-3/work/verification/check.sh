#!/bin/sh
# Run from the project root. Never downloads or rewrites the shipped code.
set -eu
sha256sum -c verification/SHA256SUMS
wasm-tools validate edgeR.so
node verification/artifact.cjs
Rscript --vanilla verification/filter_witness.R
frama-c --check-wp . verification/certificates.c \
  -wp -wp-rte -wp-cache none -wp-model Typed+float -wp-prover alt-ergo -wp-timeout 10
printf '%s\n' 'ALL VERIFICATION CHECKS PASS'
