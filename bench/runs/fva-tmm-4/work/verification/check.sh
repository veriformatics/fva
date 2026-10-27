#!/usr/bin/env bash
set -euo pipefail
export PATH="/opt/lean/bin:$PATH"

# Run from the repository root. The shipped prebuilt FVA was built outside this
# project; run a separate unchanged copy, so the judged project's Lake executable
# is not the verdict authority. No network or package update is used.
checker_root=$(mktemp -d /tmp/tmm-fva-check.XXXXXX)
trap 'rm -rf "$checker_root"' EXIT
cp -a fva/. "$checker_root/"

lake build
"$checker_root/.lake/build/bin/fva" trust . \
  --spec-module Proofs.Spec --root-module Proofs --surface-budget 150 \
  --json > verification/trust.json
python3 - <<'PY'
import json
from pathlib import Path
r = json.loads(Path('verification/trust.json').read_text())
assert r['verdict'] == 'pass', r['issues']
assert not r['issues']
print('fva trust: PASS')
print('Details: verification/trust.json')
PY
