"""Offline checks, with an FVA entry point rebuilt outside the checked project."""
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parent.parent


def run(*args, cwd=root):
    subprocess.run(args, cwd=cwd, check=True)


with tempfile.TemporaryDirectory(prefix="lz4-fva-") as temporary:
    verifier = Path(temporary) / "fva"
    shutil.copytree(root / "fva", verifier, symlinks=True)
    project_manifest = json.loads((root / "lake-manifest.json").read_text())
    manifest = verifier / "lake-manifest.json"
    data = json.loads(manifest.read_text())
    data["packagesDir"] = str((root / project_manifest["packagesDir"]).resolve())
    manifest.write_text(json.dumps(data, indent=2) + "\n")
    # Recompile and relink the entry point; keep the already built dependencies.
    # Only files in our private temporary copy are removed.
    for relative in ("lib/lean/Main.olean", "ir/Main.c.o.export", "bin/fva"):
        (verifier / ".lake/build" / relative).unlink(missing_ok=True)
    run("lake", "build", "fva", cwd=verifier)
    run("lake", "build")
    run("wasm-tools", "validate", "lz4-block-codec.wasm")
    run(str(verifier / ".lake/build/bin/fva"), "trust", str(root),
        "--spec-module", "Proofs.Spec", "--root-module", "Proofs",
        "--surface-budget", "150", "--kernel-limit", "300")
    run("python3", "verification/check_wast.py")
print("PASS: Lean build, FVA trust, artifact validation, and Wasmtime assertions")
