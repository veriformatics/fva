#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
sha256sum -c verification/subjects.sha256
lake build
node verification/artifact.cjs
Rscript --vanilla --default-packages=base,stats verification/filter.R

# Build and run the verdict tool outside the judged project, using the
# already-installed dependencies. No dependency downloads are needed.
verification_checker_parent=$(mktemp -d /tmp/edger-fva-check.XXXXXX)
trap 'rm -rf "$verification_checker_parent"' EXIT
cp -a fva "$verification_checker_parent/fva"
python3 - "$verification_checker_parent/fva" <<'PY'
import json
import sys
from pathlib import Path
checker = Path(sys.argv[1])
packages = json.loads(Path('lake-manifest.json').read_text())['packagesDir']
manifest = checker / 'lake-manifest.json'
data = json.loads(manifest.read_text())
data['packagesDir'] = packages
manifest.write_text(json.dumps(data, indent=2) + '\n')
config = checker / 'lakefile.toml'
config.write_text(config.read_text().replace('allowNonModules = true',
    'allowNonModules = true\npackagesDir = ' + json.dumps(packages)))
PY
rm "$verification_checker_parent/fva/.lake/build/bin/fva"
(cd "$verification_checker_parent/fva" && lake build fva)
"$verification_checker_parent/fva/.lake/build/bin/fva" trust . \
  --spec-module Proofs.Spec --root-module Proofs \
  | tee verification/trust.txt
echo 'All checks passed: the R1 and R2 counterexamples were reproduced.'
