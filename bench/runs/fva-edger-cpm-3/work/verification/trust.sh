#!/usr/bin/env bash
# Build the verifier outside the judged project, using the installed offline packages.
set -euo pipefail
verification_root=$(pwd)
verification_external=$(mktemp -d "${TMPDIR:-/tmp}/edger-fva-verifier-XXXXXX")
trap 'rm -rf "$verification_external"' EXIT
cp -a fva/. "$verification_external/"
python3 - "$verification_root" "$verification_external" <<'PY'
import json
from pathlib import Path
import sys
import tomllib
root, external = map(Path, sys.argv[1:])
packages = Path(tomllib.loads((root / "lakefile.toml").read_text())["packagesDir"])
if not packages.is_absolute():
    packages = (root / packages).resolve()
config = external / "lakefile.toml"
config.write_text(config.read_text().replace("allowNonModules = true",
    "allowNonModules = true\npackagesDir = " + json.dumps(str(packages))))
manifest = external / "lake-manifest.json"
data = json.loads(manifest.read_text())
data["packagesDir"] = str(packages)
manifest.write_text(json.dumps(data, indent=2) + "\n")
# Force the external executable to be rebuilt, retaining prebuilt library dependencies.
for rel in ("bin/fva", "ir/Main.c.o", "ir/Main.c.o.hash",
            "lib/lean/Main.olean", "lib/lean/Main.olean.hash"):
    (external / ".lake/build" / rel).unlink(missing_ok=True)
PY
(cd "$verification_external" && lake build fva)
"$verification_external/.lake/build/bin/fva" trust "$verification_root" \
    --spec-module Proofs.Spec --root-module Proofs
