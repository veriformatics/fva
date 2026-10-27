#!/usr/bin/env python3
"""Check pinned input bytes, rebuild proofs, audit axioms, and replay sources."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
assert Path.cwd() == root, "Run this command from the project directory"
manifest = json.loads(Path("verification/inputs.json").read_text())
for name, expected in manifest.items():
    data = Path(name).read_bytes()
    assert len(data) == expected["bytes"], f"Size mismatch: {name}"
    assert hashlib.sha256(data).hexdigest() == expected["sha256"], f"SHA-256 mismatch: {name}"
print(f"PASS: all {len(manifest)} pinned input files match their exact bytes", flush=True)


def run(command):
    print("+ " + " ".join(command), flush=True)
    p = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(p.stdout, end="", flush=True)
    assert p.returncode == 0, f"Command failed: {command}"
    assert "sorryAx" not in p.stdout, "A main result depends on sorryAx"
    return p.stdout


run(["lake", "build"])
# Explicit elaboration prints the axioms even when Lake can reuse its build.
output = run(["lake", "env", "lean", "Proofs/Results.lean"])
for name in ["R1_exact_real_fails", "R2_exact_real_fails", "R3_fails"]:
    assert f"TMM.{name}" in output, f"Missing axiom report: {name}"
run([sys.executable, "verification/replay.py"])
print("PASS: all checks completed; native_decide/compiler trust is documented in VERIFICATION.md")
