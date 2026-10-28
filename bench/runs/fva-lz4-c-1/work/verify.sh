#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"

# Check the shipped artifact and all Lean proofs, without fetching anything.
printf '%s  %s\n' \
  8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6 \
  lz4-c.wasm | sha256sum --check
wasm-tools validate lz4-c.wasm
lake build

# Build the verifier outside the project, reusing the supplied compiled dependencies.
verifier_dir=$(mktemp -d /tmp/lz4-fva-verifier.XXXXXX)
trap 'rm -rf -- "$verifier_dir"' EXIT
cp -a fva/. "$verifier_dir/"
python3 - "$verifier_dir" <<'PY'
import json
import pathlib
import sys

root = pathlib.Path(sys.argv[1])
packages = str(pathlib.Path(json.loads(pathlib.Path('lake-manifest.json').read_text())
    ['packagesDir']).resolve())
config = root / 'lakefile.toml'
config.write_text(config.read_text().replace('allowNonModules = true',
    'allowNonModules = true\npackagesDir = ' + json.dumps(packages)))
manifest = root / 'lake-manifest.json'
value = json.loads(manifest.read_text())
value['packagesDir'] = packages
manifest.write_text(json.dumps(value))
PY
rm -- "$verifier_dir/.lake/build/bin/fva" "$verifier_dir/.lake/build/bin/fva.hash"
(
  cd -- "$verifier_dir"
  lake build fva
)
mkdir -p verification
"$verifier_dir/.lake/build/bin/fva" trust . \
  --spec-module Proofs.Spec --root-module Proofs | tee verification/FVA-REPORT.txt

# An independent runtime cross-check; all comparisons trap on disagreement.
XDG_CACHE_HOME="$verifier_dir/runtime-cache" \
  wasmtime run --preload lz4=lz4-c.wasm --invoke check checks.wat
