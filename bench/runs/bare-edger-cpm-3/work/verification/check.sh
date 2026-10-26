#!/usr/bin/env bash
set -eu
sha256sum -c verification/inputs.sha256
wasm-tools validate edgeR.so
lake build
lake env lean Proofs/Counterexamples.lean
node verification/wasm.cjs
Rscript --vanilla verification/filter.R
echo 'PASS: all proofs and counterexample checks completed'
