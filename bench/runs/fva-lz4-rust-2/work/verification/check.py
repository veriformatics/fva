#!/usr/bin/env python3
"""Build an external FVA verifier and check the partial claims, entirely offline."""
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent.parent
fva = root / "fva"
manifest = (fva / "FVA/Tool/BaseManifest.lean").read_text()
for relative, digest in re.findall(r'\("([^"\n]+)",\s*"([0-9a-f]{64})"\)', manifest):
    assert hashlib.sha256((fva / relative).read_bytes()).hexdigest() == digest, relative
assert hashlib.sha256((root / "lz4-flex.wasm").read_bytes()).hexdigest() == \
    "1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775"
external = Path(tempfile.mkdtemp(prefix="lz4-fva-verifier-"))
shutil.copytree(fva, external, dirs_exist_ok=True)
packages = json.loads((root / "lake-manifest.json").read_text())["packagesDir"]
config = external / "lakefile.toml"
config.write_text(config.read_text().replace('name = "fva"',
    'packagesDir = ' + json.dumps(packages) + '\nname = "fva"', 1))
mp = external / "lake-manifest.json"
m = json.loads(mp.read_text())
m["packagesDir"] = packages
mp.write_text(json.dumps(m))
# Force rebuilding the executable outside the submitted project.
for path in [external / ".lake/build/bin/fva", external / ".lake/build/ir/Main.c.o.export",
             external / ".lake/build/ir/Main.c", external / ".lake/build/lib/lean/Main.olean"]:
    path.unlink(missing_ok=True)
subprocess.run(["lake", "build", "fva"], cwd=external, check=True)
if sys.argv[1:] == ["--prepare-only"]:
    print(external / ".lake/build/bin/fva")
    sys.exit(0)
subprocess.run(["lake", "build"], cwd=root, check=True)
print("External verifier:", external / ".lake/build/bin/fva", flush=True)
result = subprocess.run([str(external / ".lake/build/bin/fva"), "trust", str(root),
    "--spec-module", "Proofs.Spec", "--root-module", "Proofs"], cwd=root,
    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
(root / "verification/FVA-trust.txt").write_text(result.stdout)
print(result.stdout, end="", flush=True)
result.check_returncode()
print("Partial claims checked. This does not discharge README requirements R1–R3.")
