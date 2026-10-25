#!/usr/bin/env bash
# Run the pinned checker outside the project being judged; no network is needed.
set -euo pipefail
cd -- "$(dirname -- "$0")/.."
lz4_checker_dir=$(mktemp -d /tmp/lz4-fva-check.XXXXXX)
trap 'rm -rf -- "$lz4_checker_dir"' EXIT
cp -a fva "$lz4_checker_dir/fva"
python3 - "$lz4_checker_dir/fva" <<'PY'
from hashlib import sha256
import json
from pathlib import Path
import sys
checker = Path(sys.argv[1])
binary = checker / '.lake/build/bin/fva'
expected = '5a4c6e4cdeb91cd5594cc00d75c1cf70384931b8497b7e60dedbbb2b30611407'
assert sha256(binary.read_bytes()).hexdigest() == expected, 'checker binary changed'
packages = str(Path(json.loads(Path('lake-manifest.json').read_text())['packagesDir']).resolve())
config = checker / 'lakefile.toml'
config.write_text(config.read_text().replace('allowNonModules = true',
    'allowNonModules = true\npackagesDir = ' + json.dumps(packages)))
manifest = checker / 'lake-manifest.json'
data = json.loads(manifest.read_text())
data['packagesDir'] = packages
manifest.write_text(json.dumps(data, indent=2) + '\n')
PY
lake -d "$lz4_checker_dir/fva" build fva
"$lz4_checker_dir/fva/.lake/build/bin/fva" trust . \
  --spec-module Proofs.Spec --root-module Proofs --surface-budget 100
