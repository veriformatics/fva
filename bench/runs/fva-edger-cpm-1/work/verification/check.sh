#!/usr/bin/env bash
# Reproduce proofs, executable counterexamples, and the independent FVA verdict offline.
set -euo pipefail
cd "$(dirname "$0")/.."
sha256sum -c verification/sources.sha256
lake build
python3 verification/artifact_test.py
Rscript --vanilla verification/filter_test.R

# Build and run FVA from outside the verification project.
verifier_dir=$(mktemp -d /tmp/edger-fva-check.XXXXXXXX)
trap 'rm -rf "$verifier_dir"' EXIT
cp -a --reflink=auto fva/. "$verifier_dir/"
python3 - "$PWD" "$verifier_dir" <<'PY'
import json
from pathlib import Path
import sys
root, verifier = map(Path, sys.argv[1:])
manifest = json.loads((root / 'lake-manifest.json').read_text())
packages = str((root / manifest['packagesDir']).resolve())
config = verifier / 'lakefile.toml'
config.write_text('packagesDir = ' + json.dumps(packages) + '\n' + config.read_text())
manifest_path = verifier / 'lake-manifest.json'
pins = json.loads(manifest_path.read_text())
pins['packagesDir'] = packages
manifest_path.write_text(json.dumps(pins))
# Force the copied CLI entry point and executable to be rebuilt in the external directory.
for name in ['.lake/build/bin/fva', '.lake/build/lib/lean/Main.olean']:
    (verifier / name).unlink(missing_ok=True)
PY
(cd "$verifier_dir" && lake build fva)
"$verifier_dir/.lake/build/bin/fva" trust "$PWD" --spec-module Proofs.Spec --root-module Proofs
