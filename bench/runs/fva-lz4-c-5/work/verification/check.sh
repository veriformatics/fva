#!/usr/bin/env bash
# Run from the repository root. FVA is built and run outside the judged project.
set -euo pipefail
printf '%s  %s\n' 8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6 lz4-c.wasm | sha256sum --check
lake build
verifier_dir=$(mktemp -d /tmp/lz4-fva-verifier-XXXXXX)
trap 'rm -rf "$verifier_dir"' EXIT
cp -a --reflink=auto fva/. "$verifier_dir/"
python3 - "$verifier_dir" <<'PY'
import json
from pathlib import Path
import sys
external = Path(sys.argv[1])
manifest = json.loads(Path('lake-manifest.json').read_text())
manifest['packages'] = [p for p in manifest['packages'] if p['name'] != 'fva']
manifest['name'] = 'fva'
(external / 'lake-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
config = external / 'lakefile.toml'
src = config.read_text()
src = src.replace('version = "0.1.0"',
                  'version = "0.1.0"\npackagesDir = ' + json.dumps(manifest['packagesDir']))
config.write_text(src)
PY
lake --dir "$verifier_dir" build fva
"$verifier_dir/.lake/build/bin/fva" trust . --spec-module Proofs.Spec --root-module Proofs \
  --surface-budget 200 --kernel-limit 1200 | tee verification/trust.log
python3 verification/check_wasmtime.py
