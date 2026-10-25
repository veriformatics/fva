#!/usr/bin/env bash
set -euo pipefail
# Run from the project root. Pin the provided prebuilt checker before any build.
printf '%s\n' '5a4c6e4cdeb91cd5594cc00d75c1cf70384931b8497b7e60dedbbb2b30611407  fva/.lake/build/bin/fva' | sha256sum -c -
printf '%s\n' '4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf  lz4-block-codec.wasm' | sha256sum -c -
checker_dir=$(mktemp -d /tmp/lz4-fva.XXXXXX)
trap 'rm -rf "$checker_dir"' EXIT
mkdir -p "$checker_dir/.lake/build/bin" "$checker_dir/.cache/canaries"
cp fva/.lake/build/bin/fva "$checker_dir/.lake/build/bin/fva"
cp fva/lake-manifest.json "$checker_dir/"
cp -r fva/trust "$checker_dir/"
cp -r fva/.cache/canaries/arena "$checker_dir/.cache/canaries/"
wasm-tools validate lz4-block-codec.wasm
lake build
"$checker_dir/.lake/build/bin/fva" trust . --spec-module Proofs.Spec --root-module Proofs --surface-budget 100
python3 witnesses/runtime.py
