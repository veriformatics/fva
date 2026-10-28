#!/usr/bin/env bash
# Offline reproduction, including an FVA executable linked outside this project.
set -euo pipefail
cd -- "$(dirname -- "$0")/.."
project_dir="$PWD"
printf '%s\n' '8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6  lz4-c.wasm' | sha256sum -c -
lake build
python3 verification/runtime_cases.py
audit_dir="$(mktemp -d "${TMPDIR:-/tmp}/lz4-fva-verifier.XXXXXXXX")"
trap 'rm -rf -- "$audit_dir"' EXIT
cp -a --reflink=auto fva/. "$audit_dir/"
python3 - "$project_dir" "$audit_dir" <<'PY'
import json
from pathlib import Path
import sys
project, audit = map(Path, sys.argv[1:])
packages = Path(json.loads((project / 'lake-manifest.json').read_text())['packagesDir'])
if not packages.is_absolute():
    packages = (project / packages).resolve()
manifest = audit / 'lake-manifest.json'
content = json.loads(manifest.read_text())
content['packagesDir'] = str(packages)
manifest.write_text(json.dumps(content, indent=2) + '\n')
config = audit / 'lakefile.toml'
content = config.read_text()
content = content.replace('allowNonModules = true',
                          'allowNonModules = true\npackagesDir = ' + json.dumps(str(packages)))
config.write_text(content)
# Require the final executable to be linked in this outside copy.
(audit / '.lake/build/bin/fva').unlink(missing_ok=True)
PY
lake -d "$audit_dir" build fva
"$audit_dir/.lake/build/bin/fva" trust "$project_dir" \
  --spec-module Proofs.Spec --root-module Proofs --surface-budget 100 \
  | tee verification/fva-trust.txt
