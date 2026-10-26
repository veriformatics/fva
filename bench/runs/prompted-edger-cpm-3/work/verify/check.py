"""One offline check: byte identity, execution witnesses, independent kernels, canaries."""
import collections
import copy
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
from runtime import ROOT, OUT, prepare, matrix

TARGETS = ["Evidence.r1_witness", "Evidence.r2_total", "Evidence.r2_tolerance"]
os.chdir(ROOT)
OUT.mkdir(exist_ok=True)


def call(args, log, env=None, reject=None):
    result = subprocess.run([str(a) for a in args], text=True, capture_output=True, env=env)
    output = result.stdout + result.stderr
    (OUT / log).write_text(output)
    if reject is None:
        if result.returncode != 0:
            raise RuntimeError(f"{args}:\n{output}")
    elif result.returncode == 0 or reject not in output:
        raise RuntimeError(f"Expected a type-checking rejection from {args}:\n{output}")
    return result.stdout


def integrity():
    for line in (ROOT / "verify/inputs.sha256").read_text().splitlines():
        digest, name = line.split("  ")
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, name


def read_export(path):
    objects = [json.loads(line) for line in path.read_text().splitlines()]
    names = {0: ""}
    for obj in objects:
        if "in" in obj:
            part = obj.get("str", obj.get("num"))
            names[obj["in"]] = ".".join(filter(None, [names[part["pre"]], str(part.get("str", part.get("i")))]))
        assert "axiom" not in obj, "No axioms (including sorry/trustCompiler) are permitted"
    return objects, names


def kernels(path, prefix, bad=False):
    config = OUT / f"{prefix}.json"
    config.write_text(json.dumps({
        "export_file_path": str(path), "permitted_axioms": [],
        "unpermitted_axiom_hard_error": True, "nat_extension": True,
        "string_extension": True, "print_success_message": True,
    }, indent=2) + "\n")
    lean = call([BIN / "leanchecker", "--from-export", path], f"{prefix}.lean.log",
                reject="declaration type mismatch" if bad else None)
    rust = call([BIN / "nanoda_bin", config], f"{prefix}.nanoda.log",
                reject="assertion failed: self.def_eq(u, v)" if bad else None)
    if not bad:
        assert "Lean default kernel accepts the solution" in lean
        assert "with no typechecker errors" in rust


integrity()
print("PASS: original artifact, sources, requirements and documentation hashes", flush=True)
prepare()
overflow = matrix(1, 1, [2.0**1020], [2.0**1020])[0]
assert math.isinf(overflow) and overflow > 0
assert (2**1020 * 1000000) == (1000000 * 2**1020)
assert 2.0**1020 / 2.0**1020 * 1000000 == 1000000
assert matrix(1, 1, [1], [1]) == [1000000]
print("R1 COUNTEREXAMPLE: c=L=2^1020; expected 1000000; actual +infinity (bits 0x7ff0000000000000)", flush=True)
r_output = call(["Rscript", "--vanilla", "verify/filter.R"], "filter.log")
print(r_output, end="", flush=True)

BIN = Path(call(["lean", "--print-prefix"], "lean-prefix.log").strip()) / "bin"
# Compile the proof sources freshly, without relying on Lake's build cache.
lib = ROOT / ".lake/build/lib/lean"
(lib / "Proofs").mkdir(parents=True, exist_ok=True)
call(["lake", "env", "lean", "-o", lib / "Proofs/Arithmetic.olean", "Proofs/Arithmetic.lean"], "compile-arithmetic.log")
call(["lake", "env", "lean", "-o", lib / "Proofs.olean", "Proofs.lean"], "compile-root.log")
export = OUT / "proofs.ndjson"
export.write_text(call(["lake", "env", BIN / "leanexport", "Proofs", "--", *TARGETS], "export.log"))
objects, names = read_export(export)
theorems = {names[obj["thm"]["name"]] for obj in objects if "thm" in obj}
assert set(TARGETS) <= theorems, "Missing theorem; checking an empty export is not success"
kernels(export, "proofs")
print("PASS: all three arithmetic theorems replay in Lean's kernel and Nanoda's independent Rust kernel; zero axioms", flush=True)

# First check well-typed canaries, then corrupt their types, keeping their
# proof terms. Move each changed theorem last so both exports are well-scoped.
call(["lake", "env", "lean", "-R", "verify", "-o", OUT / "Canary.olean", "verify/Canary.lean"], "compile-canary.log")
env = dict(os.environ, LEAN_PATH=str(OUT))
canary = OUT / "canary.ndjson"
canary.write_text(call([BIN / "leanexport", "Canary", "--", "Canary.trueProof", "Canary.zeroEquality", "Canary.falseType", "Canary.unequalType"], "canary-export.log", env=env))
canaries, canary_names = read_export(canary)
kernels(canary, "canary")
for tag, theorem, false_type in [
    ("false", "Canary.trueProof", "Canary.falseType"),
    ("zero-equals-one", "Canary.zeroEquality", "Canary.unequalType"),
]:
    poisoned = copy.deepcopy(canaries)
    index = next(i for i, obj in enumerate(poisoned) if "thm" in obj and canary_names[obj["thm"]["name"]] == theorem)
    changed = poisoned.pop(index)
    changed["thm"]["type"] = next(obj["def"]["value"] for obj in poisoned if "def" in obj and canary_names[obj["def"]["name"]] == false_type)
    poisoned.append(changed)
    bad_path = OUT / f"{tag}.ndjson"
    bad_path.write_text("\n".join(json.dumps(obj) for obj in poisoned) + "\n")
    kernels(bad_path, tag, bad=True)
call(["lake", "env", "lean", "verify/Bad.lean"], "bad-frontend.log", reject="Type mismatch")
print("PASS: both kernels reject False := True.intro and 0=1 := Eq.refl 0; Lean also rejects the false source proof", flush=True)

inventory = {}
for name in ["Proofs.lean", "Proofs/Arithmetic.lean", "verify/runtime.py", "verify/filter.R", "verify/check.py", "verify/Canary.lean", "verify/Bad.lean", "verify/inputs.sha256"]:
    data = (ROOT / name).read_bytes()
    inventory[name] = {"lines": len(data.splitlines()), "bytes": len(data)}
declarations = collections.Counter()
for obj in objects:
    for kind in ["def", "thm", "axiom", "opaque", "quot"]:
        if kind in obj:
            declarations[kind] += 1
    for kind, values in obj.get("inductive", {}).items():
        declarations[kind] += len(values)
inventory["export"] = {"declarations": dict(declarations), "total_declarations": sum(declarations.values()), "bytes": export.stat().st_size}
(OUT / "sizes.json").write_text(json.dumps(inventory, indent=2) + "\n")
integrity()
print("PASS: inputs remain unchanged; sizes in .verification/sizes.json; checker logs and exports in .verification/", flush=True)
print("VERIFICATION PASSED: R1 and R2 are refuted by the reproduced witnesses; supporting proofs and negative controls passed.", flush=True)
