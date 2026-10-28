#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 checks/run_examples.py
wasm-tools validate lz4-c.wasm
lake build
verification_reference=$(mktemp -d /tmp/fva-lz4-checker.XXXXXX)
trap 'rm -rf "$verification_reference"' EXIT
cp -a fva/. "$verification_reference/"
python3 - "$verification_reference" <<'PY'
import json
from pathlib import Path
import sys
reference = Path(sys.argv[1])
packages = (Path.cwd() / json.loads(Path('lake-manifest.json').read_text())['packagesDir']).resolve()
config = reference / 'lakefile.toml'
config.write_text(config.read_text().replace('allowNonModules = true',
    f'allowNonModules = true\npackagesDir = {json.dumps(str(packages))}'))
manifest = reference / 'lake-manifest.json'
data = json.loads(manifest.read_text())
data['packagesDir'] = str(packages)
manifest.write_text(json.dumps(data))
PY
rm "$verification_reference/.lake/build/bin/fva"
lake --no-cache -d "$verification_reference" build fva
"$verification_reference/.lake/build/bin/fva" trust . \
  --spec-module Proofs.Spec --root-module Proofs | tee checks/fva-trust.txt
