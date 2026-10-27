#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

sha256sum -c verification/inputs.sha256
lake build

# Build the verdict executable outside the judged project, using the untouched
# FVA source and the already-installed, pinned packages. No network is used.
tmm_checker_dir="$(mktemp -d /tmp/fva-tmm-check.XXXXXX)"
cp -a fva/. "$tmm_checker_dir/"
tmm_packages_dir="$(python3 -c 'import json; print(json.load(open("lake-manifest.json"))["packagesDir"])')"
if [[ "$tmm_packages_dir" != /* ]]; then
  tmm_packages_dir="$PWD/$tmm_packages_dir"
fi
if [[ ! -e "$tmm_checker_dir/.lake/packages" ]]; then
  ln -s "$tmm_packages_dir" "$tmm_checker_dir/.lake/packages"
fi
rm -f -- "$tmm_checker_dir/.lake/build/bin/fva" "$tmm_checker_dir/.lake/build/bin/fva.trace"
lake -d "$tmm_checker_dir" build fva
"$tmm_checker_dir/.lake/build/bin/fva" trust . \
  --spec-module Proofs.Spec --root-module Proofs --kernel-limit 1200 \
  | tee verification/trust.txt
printf 'Independent checker: %s\n' "$tmm_checker_dir/.lake/build/bin/fva"
