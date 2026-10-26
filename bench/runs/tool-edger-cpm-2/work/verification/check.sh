#!/usr/bin/env bash
set -euo pipefail
# Run from the project root. Each stage must succeed.
sha256sum -c verification/inputs.sha256
frama-c --check-wp . verification/wp.c -wp -wp-rte -wp-prover alt-ergo -wp-timeout 10 -wp-cache none -wp-verbose 2 | tee verification/wp.log
node verification/artifact.mjs | tee verification/artifact.log
Rscript --vanilla verification/filter.R | tee verification/filter.log
echo 'VERIFICATION CHECKS PASS (both requirements have counterexamples)'
