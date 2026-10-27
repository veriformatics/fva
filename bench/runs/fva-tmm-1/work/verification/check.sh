#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Freeze the already-built verifier outside the subject project before it builds.
verify_dir=$(mktemp -d /tmp/tmm-fva-verifier.XXXXXX)
trap 'rm -rf "$verify_dir"' EXIT
mkdir -p "$verify_dir/.lake/build/bin"
cp fva/.lake/build/bin/fva "$verify_dir/.lake/build/bin/fva"
cp fva/lake-manifest.json "$verify_dir/lake-manifest.json"
cp -r fva/trust fva/.cache "$verify_dir/"
"$verify_dir/.lake/build/bin/fva" trust . \
  --spec-module Proofs.Spec --root-module Proofs --surface-budget 200 \
  | tee verification/fva-trust.txt
