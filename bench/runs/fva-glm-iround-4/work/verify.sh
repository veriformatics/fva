#!/usr/bin/env bash
# Recheck the artifact and proofs offline with an FVA checker outside the project.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
printf '%s  %s\n' eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a glm-iround.wasm | sha256sum -c -
lake build
checker=$(mktemp -d /tmp/fva-iround-check.XXXXXX)
trap 'rm -rf -- "$checker"' EXIT
cp -a --reflink=auto fva/. "$checker/"
python3 - "$checker" <<'PY'
import json
import pathlib
import sys
root = pathlib.Path(sys.argv[1])
packages = json.loads(pathlib.Path('lake-manifest.json').read_text())['packagesDir']
packages = str(pathlib.Path(packages).resolve())
config = root / 'lakefile.toml'
config.write_text(config.read_text().replace(
    'allowNonModules = true',
    'allowNonModules = true\npackagesDir = ' + json.dumps(packages)))
manifest = root / 'lake-manifest.json'
data = json.loads(manifest.read_text())
data['packagesDir'] = packages
manifest.write_text(json.dumps(data, indent=2) + '\n')
PY
# Relink the executable in the external package, using the installed build cache.
rm -- "$checker/.lake/build/bin/fva"
lake -d "$checker" build fva
"$checker/.lake/build/bin/fva" trust . --spec-module Proofs.Spec --root-module Proofs | tee fva-trust.txt
