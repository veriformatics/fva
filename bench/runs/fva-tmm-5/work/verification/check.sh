#!/usr/bin/env bash
# Run from the project root. No network access is needed.
set -euo pipefail
lake build
checker_dir=$(mktemp -d /tmp/tmm-fva-checker.XXXXXX)
cp -a fva/. "$checker_dir/"
python - "$checker_dir" <<'PY'
import json
import pathlib
import sys
root = pathlib.Path(sys.argv[1])
project_manifest = json.loads(pathlib.Path('lake-manifest.json').read_text())
packages = str(pathlib.Path(project_manifest['packagesDir']).resolve())
manifest = json.loads((root / 'lake-manifest.json').read_text())
manifest['packagesDir'] = packages
(root / 'lake-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
config = root / 'lakefile.toml'
config.write_text(config.read_text().replace(
    'allowNonModules = true',
    'allowNonModules = true\npackagesDir = ' + json.dumps(packages)))
PY
rm -f "$checker_dir/.lake/build/bin/fva" "$checker_dir/.lake/build/bin/fva.trace"
(cd "$checker_dir" && lake build fva)
"$checker_dir/.lake/build/bin/fva" trust . --spec-module Proofs.Spec --root-module Proofs
