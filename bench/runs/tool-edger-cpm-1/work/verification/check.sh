#!/bin/sh
# Run from the repository root. No network access or Lean build is required.
set -eu
sha256sum -c verification/inputs.sha256
python3 verification/check_artifact.py
Rscript verification/check_filter.R
frama-c --check-wp . verification/witnesses.c \
    -wp -wp-rte -wp-model Typed+float -wp-prover qed,alt-ergo -wp-timeout 10 -wp-cache none
printf '%s\n' 'PASS: all counterexample replays and all WP goals checked'
