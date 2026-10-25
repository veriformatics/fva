#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
python3 verification/replay.py

# Rebuild the unchanged FVA implementation outside the project being judged.
verifier_dir=$(mktemp -d /tmp/lz4-fva-check.XXXXXXXX)
trap 'rm -rf "$verifier_dir"' EXIT
cp -a fva "$verifier_dir/fva"
python3 - "$verifier_dir/fva" <<'PY'
import json
from pathlib import Path
import sys

external = Path(sys.argv[1])
root_manifest = json.loads(Path("lake-manifest.json").read_text())
packages = str(Path(root_manifest["packagesDir"]).resolve())
manifest = external / "lake-manifest.json"
data = json.loads(manifest.read_text())
data["packagesDir"] = packages
manifest.write_text(json.dumps(data))
config = external / "lakefile.toml"
config.write_text(config.read_text().replace(
    "allowNonModules = true", "allowNonModules = true\npackagesDir = " + json.dumps(packages)))
for filename in ["fva", "fva.trace", "fva.hash"]:
    (external / ".lake/build/bin" / filename).unlink(missing_ok=True)
PY
(cd "$verifier_dir/fva" && lake build fva)
"$verifier_dir/fva/.lake/build/bin/fva" trust . \
  --spec-module Proofs.Spec --root-module Proofs | tee verification/trust.txt
