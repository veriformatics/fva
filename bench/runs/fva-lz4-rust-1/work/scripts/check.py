#!/usr/bin/env python3
"""Rebuild the proof project, run concrete Wasmtime checks, and replay FVA claims."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent.parent
EXPECTED = "1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775"


def run(args, cwd=ROOT):
    print("+", " ".join(map(str, args)), flush=True)
    subprocess.run(list(map(str, args)), cwd=cwd, check=True)


def main():
    artifact = (ROOT / "lz4-flex.wasm").read_bytes()
    assert len(artifact) == 7161 and hashlib.sha256(artifact).hexdigest() == EXPECTED
    run(["lake", "build"])
    with tempfile.TemporaryDirectory(prefix="lz4-verification-") as tmp:
        tmp = Path(tmp)
        wast = tmp / "cases.wast"
        run(["lake", "env", "lean", "--run", "scripts/runtime.lean", wast])
        run(["wasmtime", "wast", "-C", "cache=n", wast])
        print("Wasmtime: all 16 cases passed.", flush=True)

        # Use a separate verifier tree. Project FVA sources are never edited.
        verifier = tmp / "fva"
        shutil.copytree(ROOT / "fva", verifier, symlinks=True)
        packages = Path(json.loads((ROOT / "lake-manifest.json").read_text())["packagesDir"])
        if not packages.is_absolute():
            packages = ROOT / packages
        packages = str(packages.resolve())
        config = verifier / "lakefile.toml"
        config.write_text(config.read_text().replace(
            "allowNonModules = true",
            "allowNonModules = true\npackagesDir = " + json.dumps(packages)))
        manifest = verifier / "lake-manifest.json"
        data = json.loads(manifest.read_text())
        data["packagesDir"] = packages
        manifest.write_text(json.dumps(data, indent=2) + "\n")
        # Force an executable link in the separate tree, using installed build products.
        for name in ("fva", "fva.hash", "fva.trace"):
            (verifier / ".lake/build/bin" / name).unlink(missing_ok=True)
        run(["lake", "build", "fva"], cwd=verifier)
        args = [verifier / ".lake/build/bin/fva", "trust", ROOT,
                "--spec-module", "Proofs.Spec", "--root-module", "Proofs"]
        print("+", " ".join(map(str, args)), flush=True)
        result = subprocess.run(list(map(str, args)), cwd=ROOT,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        report = ROOT / "verification/trust.txt"
        report.parent.mkdir(exist_ok=True)
        report.write_text(result.stdout)
        print(result.stdout, end="", flush=True)
        result.check_returncode()
    print("PARTIAL CLAIMS CHECKED. Full R1, R2, and R3 remain unproved.", flush=True)


if __name__ == "__main__":
    main()
