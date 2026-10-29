#!/usr/bin/env python3
"""Recheck the partial Lean results and supplementary runtime tests, offline."""
import hashlib
import json
import pathlib
import subprocess
import tempfile
import tomllib

ROOT = pathlib.Path(__file__).resolve().parents[1]
SHA256 = "1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775"


def run(argv, *, check=True, **kwargs):
    print("+", " ".join(map(str, argv)), flush=True)
    return subprocess.run(argv, cwd=ROOT, check=check, **kwargs)


def main():
    binary = (ROOT / "lz4-flex.wasm").read_bytes()
    assert len(binary) == 7161 and hashlib.sha256(binary).hexdigest() == SHA256
    run(["wasm-tools", "validate", "lz4-flex.wasm"])
    run(["lake", "build"])
    packages = tomllib.loads((ROOT / "lakefile.toml").read_text())["packagesDir"]
    # Preserve FVA's supplied source and pinned base manifest. Only dependency
    # locations change in this external copy; the executable is relinked there.
    with tempfile.TemporaryDirectory(prefix="lz4-fva-audit-", dir="/tmp") as tmp:
        package = pathlib.Path(tmp) / "fva"
        run(["cp", "-a", "--reflink=auto", str(ROOT / "fva"), str(package)])
        config = package / "lakefile.toml"
        config.write_text(config.read_text().replace(
            "allowNonModules = true", f"allowNonModules = true\npackagesDir = {json.dumps(packages)}"))
        manifest = package / "lake-manifest.json"
        value = json.loads(manifest.read_text())
        value["packagesDir"] = packages
        manifest.write_text(json.dumps(value))
        (package / ".lake/build/bin/fva").unlink(missing_ok=True)
        run(["lake", "-d", str(package), "build", "fva"])
        verdict = run([str(package / ".lake/build/bin/fva"), "trust", ".",
                       "--spec-module", "Proofs.Spec", "--root-module", "Proofs",
                       "--surface-budget", "200", "--kernel-limit", "1200"],
                      check=False, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        print(verdict.stdout, end="")
        (ROOT / "verification/TRUST.txt").write_text(verdict.stdout)
        verdict.check_returncode()
    run(["python3", "verification/runtime_checks.py"])
    print("PASS: all delivered partial claims checked; universal R1–R3 remain UNPROVED")


if __name__ == "__main__":
    main()
