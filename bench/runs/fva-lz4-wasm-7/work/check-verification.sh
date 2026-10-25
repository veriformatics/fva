#!/usr/bin/env bash
set -euo pipefail

# Run from the project directory, using only the installed offline dependencies.
lake build
wasm-tools validate lz4-block-codec.wasm
node counterexamples.mjs

# Rebuild the audit executable outside the subject project.
audit_dir=$(mktemp -d /tmp/lz4-fva-check.XXXXXX)
cp -a --reflink=auto fva/. "$audit_dir/"
python3 - "$audit_dir" <<'PY'
import json
import pathlib
import sys
root = pathlib.Path(sys.argv[1])
packages = str(pathlib.Path(json.load(open('lake-manifest.json'))['packagesDir']).resolve())
p = root / 'lakefile.toml'
s = p.read_text().replace('name = "fva"', 'name = "fva"\npackagesDir = ' + json.dumps(packages), 1)
p.write_text(s)
p = root / 'lake-manifest.json'
x = json.loads(p.read_text())
x['packagesDir'] = packages
p.write_text(json.dumps(x, indent=2) + '\n')
PY
rm -f "$audit_dir/.lake/build/bin/fva"
(
  cd "$audit_dir"
  lake build fva
)
"$audit_dir/.lake/build/bin/fva" trust . --spec-module Proofs.Spec --root-module Proofs --json > TRUST.json
python3 - <<'PY'
import json
r = json.load(open('TRUST.json'))
assert r['verdict'] == 'pass' and r['issues'] == [], r
print('FVA PASS: three artifact counterexamples; no audit issues.')
print('Kernel replay:', r['report']['replay'])
print('Review surface:', r['report']['reviewModules'])
PY
