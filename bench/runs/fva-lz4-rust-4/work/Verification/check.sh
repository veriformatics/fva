#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
wasm-tools validate lz4-flex.wasm

# Build the unchanged FVA sources outside the judged project, using the offline cache.
task_verifier=$(mktemp -d "${TMPDIR:-/tmp}/lz4-fva-check.XXXXXX")
trap 'rm -rf -- "$task_verifier"' EXIT
cp -a fva/. "$task_verifier/"
python3 - "$task_verifier" <<'PY'
import json
from pathlib import Path
import sys

target = Path(sys.argv[1])
packages = str(Path(json.loads(Path('lake-manifest.json').read_text())['packagesDir']).resolve())
manifest = target / 'lake-manifest.json'
data = json.loads(manifest.read_text())
data['packagesDir'] = packages
manifest.write_text(json.dumps(data, indent=2) + '\n')
config = target / 'lakefile.toml'
config.write_text(config.read_text().replace(
    'allowNonModules = true', 'allowNonModules = true\npackagesDir = ' + json.dumps(packages)))
for file in (target / '.lake/build/bin').glob('fva*'):
    if file.is_file():
        file.unlink()
PY
lake -d "$task_verifier" build fva
lake build
"$task_verifier/.lake/build/bin/fva" trust . \
  --spec-module Proofs.Spec --root-module Proofs --surface-budget 60
python3 Verification/run_samples.py
printf '%s\n' 'Only the stated partial claims were proved; R1–R3 remain unproved in full.'
