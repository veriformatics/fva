#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
sha256sum -c verification/artifact.sha256
wasm-tools validate lz4-flex.wasm
for target in EmptyBlock LiteralBlock OverlappingBlock ZeroOffset ExcessiveOffset InsufficientCapacity TruncatedLength; do
  lake build "Proofs.$target"
done
lake build
verifier_dir=$(mktemp -d /tmp/fva-verifier.XXXXXX)
trap 'rm -rf "$verifier_dir"' EXIT
cp -a --reflink=auto fva/. "$verifier_dir/"
packages_dir=$(python3 -c 'import json,pathlib; p=pathlib.Path(json.load(open("lake-manifest.json"))["packagesDir"]); print(p.resolve())')
if [ ! -e "$verifier_dir/.lake/packages" ]; then
  ln -s "$packages_dir" "$verifier_dir/.lake/packages"
fi
rm -f "$verifier_dir/.lake/build/bin/fva"
lake -d "$verifier_dir" build fva
"$verifier_dir/.lake/build/bin/fva" trust . --spec-module Proofs.Spec --root-module Proofs
node verification/search.mjs
