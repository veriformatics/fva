#!/usr/bin/env bash
set -euo pipefail
# Run from the repository root. Build the supplied, unchanged FVA package outside
# the project, using its prebuilt libraries and the installed pinned packages.
base=$(mktemp -d /tmp/fva-tmm-check.XXXXXX)
cp -a fva/. "$base/"
packages=$(python3 -c 'import json,pathlib; print(pathlib.Path(json.load(open("lake-manifest.json"))["packagesDir"]).resolve())')
ln -s "$packages" "$base/.lake/packages"
rm "$base/.lake/build/bin/fva"
lake -d "$base" build fva
lake build
"$base/.lake/build/bin/fva" trust . --spec-module Proofs.Spec --root-module Proofs \
  --surface-budget 200 | tee verification/trust.txt
