#!/usr/bin/env python3
"""Reproduce the artifact counterexample and replay the arithmetic certificates."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
os.chdir(ROOT)
OUT = ROOT / ".verification"
OUT.mkdir(exist_ok=True)


def run(args, *, stdin=None, output=None, reject=False):
    result = subprocess.run(args, input=stdin, capture_output=True)
    if output:
        Path(output).write_bytes(result.stdout + result.stderr)
    if reject:
        if result.returncode == 0:
            raise RuntimeError(f"FALSE PROOF ACCEPTED: {args}")
    elif result.returncode != 0:
        raise RuntimeError(f"Failed: {args}\n{result.stdout.decode()}\n{result.stderr.decode()}")
    return result


artifact = Path("glm-iround.wasm").read_bytes()
if len(artifact) != 66 or hashlib.sha256(artifact).hexdigest() != (
    "eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a"
):
    raise RuntimeError("Shipped artifact bytes differ from README's artifact")
run(["wasm-tools", "validate", "glm-iround.wasm"])
run(["wasm-tools", "print", "glm-iround.wasm"], output=OUT / "artifact.wat")
run(["wasm-tools", "validate", "verification/call.wat"])
for compiler in ("cranelift", "winch"):
    result = run([
        "wasmtime", "run", "-C", f"cache=n,compiler={compiler}",
        "--preload", "artifact=glm-iround.wasm", "--invoke", "counterexample",
        "verification/call.wat",
    ], output=OUT / f"execution-{compiler}.log")
    if result.stdout.strip() != b"1":
        raise RuntimeError(f"{compiler}: expected the observed result 1")
print("Artifact pinned (66 bytes); exact bits 0x3fdfffffffffffff return 1 in both backends.", flush=True)

# Compile the actual proof source afresh, regardless of Lake's incremental cache.
prefix = Path(run(["lake", "env", "lean", "--print-prefix"]).stdout.decode().strip())
module = Path(".lake/build/lib/lean/Proofs/Counterexample.olean")
module.parent.mkdir(parents=True, exist_ok=True)
run(["lake", "env", "lean", "-o", str(module), "Proofs/Counterexample.lean"],
    output=OUT / "compile.log")
roots = ["Verification.input_encoding", "Verification.r1_counterexample", "Verification.strictly_closer"]
export = run(["lake", "env", str(prefix / "bin/leanexport"),
              "Proofs.Counterexample", "--", *roots]).stdout
(OUT / "proofs.jsonl").write_bytes(export)

# Enforce an axiom allowlist and find the exact certificates in the export.
records = [json.loads(line) for line in export.splitlines()]
names = {0: ""}
for obj in records:
    if "in" in obj:
        part = obj.get("str", obj.get("num"))
        suffix = str(part.get("str", part.get("i")))
        names[obj["in"]] = ".".join(filter(None, [names[part["pre"]], suffix]))
axioms = {names[obj["axiom"]["name"]] for obj in records if "axiom" in obj}
allowed = set()
if not axioms <= allowed:
    raise RuntimeError(f"Unexpected axioms: {axioms - allowed}")
theorems = {names[obj["thm"]["name"]] for obj in records if "thm" in obj}
if not set(roots) <= theorems:
    raise RuntimeError("Export is missing a requested theorem")
false_expr = next(obj["ie"] for obj in records
                  if "const" in obj and names[obj["const"]["name"]] == "False")


def replay(data, label, reject=False):
    path = OUT / f"{label}.jsonl"
    path.write_bytes(data)
    lean = run([str(prefix / "bin/leanchecker-paranoid"), "--from-export", str(path)],
               output=OUT / f"{label}-lean.log", reject=reject)
    nanoda = run([str(prefix / "bin/nanoda_bin"), "verification/nanoda.json"], stdin=data,
                 output=OUT / f"{label}-nanoda.log", reject=reject)
    if reject and b"(kernel) declaration type mismatch" not in lean.stdout + lean.stderr:
        raise RuntimeError("Lean control did not fail with the intended type error")
    if reject and b"assertion failed: self.def_eq(u, v)" not in nanoda.stdout + nanoda.stderr:
        raise RuntimeError("Nanoda control did not fail with the intended type error")


replay(export, "positive")
print("Lean kernel and independent Nanoda kernel accepted all three certificates.", flush=True)
# Preserve valid JSON, declarations and original proof terms, but claim False.
# These are type errors, not parse errors or merely failed proof tactics.
for index, target in enumerate(roots[1:]):
    changed = 0
    mutant = []
    for obj in records:
        if "thm" in obj and names[obj["thm"]["name"]] == target:
            obj = {"thm": dict(obj["thm"], type=false_expr)}
            changed += 1
        mutant.append(json.dumps(obj, separators=(",", ":")))
    if changed != 1:
        raise RuntimeError(f"Expected exactly one mutation of {target}")
    replay(("\n".join(mutant) + "\n").encode(), f"false-{index}", reject=True)
print("Both kernels rejected both forged proofs of False.", flush=True)
print(f"Export: {len(export)} bytes; axioms: {sorted(axioms)}.", flush=True)
print("PASS: R1 is REFUTED; arithmetic proofs replayed; false-proof controls rejected.")
