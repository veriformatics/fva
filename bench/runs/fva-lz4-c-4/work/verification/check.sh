#!/usr/bin/env bash
# Run from the project root. All dependencies must already be installed.
set -euo pipefail
lake build
python3 verification/examples.py

# Rebuild the verifier outside the judged project from the unedited FVA sources.
verifier_dir=$(mktemp -d /tmp/lz4-fva-verifier.XXXXXXXX)
trap 'rm -rf -- "$verifier_dir"' EXIT
cp -a fva/. "$verifier_dir/"
python3 - "$verifier_dir" <<'PY'
import json
from pathlib import Path
import sys
root = Path(sys.argv[1])
packages = Path(json.loads(Path("lake-manifest.json").read_text())["packagesDir"]).resolve()
config = root / "lakefile.toml"
config.write_text(config.read_text().replace(
    "allowNonModules = true",
    "allowNonModules = true\npackagesDir = " + json.dumps(str(packages)), 1))
manifest = root / "lake-manifest.json"
data = json.loads(manifest.read_text())
data["packagesDir"] = str(packages)
manifest.write_text(json.dumps(data))
(root / ".lake/build/bin/fva").unlink(missing_ok=True)
PY
(cd "$verifier_dir" && lake build fva)
"$verifier_dir/.lake/build/bin/fva" trust . \
    --spec-module Proofs.Spec --root-module Proofs --json > verification/trust.json
python3 - <<'PY'
import json
from pathlib import Path
report = json.loads(Path("verification/trust.json").read_text())
assert report["verdict"] == "pass", report["issues"]
print("FVA PASS for the finite examples; R1, R2, and R3 remain unresolved.")
print("Read verification/trust.json for the kernel, artifact-link, and review-surface results.")
PY
