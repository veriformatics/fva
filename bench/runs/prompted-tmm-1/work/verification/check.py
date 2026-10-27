#!/usr/bin/env python3
"""Rebuild, bind, audit, independently replay, and challenge the proof setup."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent.parent
os.chdir(ROOT)
BUILD = ROOT / ".verification-build"
BUILD.mkdir(exist_ok=True)
(BUILD / "Proofs").mkdir(exist_ok=True)
ENV = dict(os.environ, LEAN_PATH=str(BUILD))
BIN = Path(shutil.which("lean")).resolve().parent
TARGETS = ["Artifacts." + n for n in (
    "artifact_values", "r1_necessary_conditions", "r2_necessary_conditions",
    "r3_all_samples_fail", "r3_sample1_gap", "r3_failure_of_artifact")]
AXIOMS = {"propext", "Quot.sound"}
ARTIFACTS = {"Artifacts.edgeBytes": ROOT / "edger-factors.txt",
             "Artifacts.rnaBytes": ROOT / "rnanorm-factors.txt"}


def run(args, log, *, reject=None, output=None):
    result = subprocess.run(list(map(str, args)), env=ENV, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (BUILD / log).write_text(result.stdout)
    if output is not None:
        Path(output).write_text(result.stdout)
    if reject is None:
        if result.returncode != 0:
            raise RuntimeError(f"{args} failed:\n{result.stdout}")
    elif result.returncode == 0 or reject not in result.stdout:
        raise RuntimeError(f"Negative control did not give the expected rejection: {args}\n{result.stdout}")
    return result.stdout


def audit(path, *, targets=TARGETS, artifacts=ARTIFACTS):
    export_bytes = Path(path).stat().st_size
    names, exprs, declarations = {0: ""}, {}, {}
    for line in Path(path).read_text().splitlines():
        row = json.loads(line)
        if "in" in row:
            if "str" in row:
                pre, suffix = row["str"]["pre"], row["str"]["str"]
            else:
                pre, suffix = row["num"]["pre"], str(row["num"]["i"])
            names[row["in"]] = (names[pre] + "." if pre else "") + suffix
        if "ie" in row:
            exprs[row["ie"]] = row
        for kind in ("axiom", "def", "opaque", "thm"):
            if kind in row:
                data = row[kind]
                name = names[data["name"]]
                if name in declarations:
                    raise RuntimeError("duplicate declaration: " + name)
                declarations[name] = kind, data
    axioms = {n for n, (k, _) in declarations.items() if k == "axiom"}
    if not axioms <= AXIOMS:
        raise RuntimeError("unapproved axioms: " + str(axioms - AXIOMS))
    for name in targets:
        if name not in declarations or declarations[name][0] != "thm":
            raise RuntimeError("missing proved target: " + name)
    for name, path in artifacts.items():
        kind, data = declarations[name]
        if kind != "def" or exprs[data["value"]].get("strVal", "").encode("utf-8") != path.read_bytes():
            raise RuntimeError("artifact bytes mismatch: " + name)
    counts = {k: sum(kind == k for kind, _ in declarations.values())
              for k in ("axiom", "def", "opaque", "thm")}
    return dict(counts=counts, axioms=sorted(axioms), export_bytes=export_bytes)


def nanoda(bundle, label, *, reject=None):
    config = dict(export_file_path=str(bundle), permitted_axioms=sorted(AXIOMS),
                  unpermitted_axiom_hard_error=True, nat_extension=True,
                  string_extension=True, pp_declars=[], pp_to_stdout=False,
                  print_success_message=True)
    path = BUILD / (label + ".json")
    path.write_text(json.dumps(config, indent=2) + "\n")
    return run([BIN / "nanoda_bin", path], label + ".log", reject=reject)


# Pin the original input, source, documentation, and output bytes before any run.
for line in Path("verification/inputs.sha256").read_text().splitlines():
    expected, name = line.split("  ", 1)
    if hashlib.sha256(Path(name).read_bytes()).hexdigest() != expected:
        raise RuntimeError("original input changed: " + name)
print("Original input/source/document/output byte identities: OK", flush=True)
version = run([BIN / "lean", "--version"], "lean-version.log")
if "version 4.35.0," not in version:
    raise RuntimeError("Lean 4.35.0 required: " + version)

# Always elaborate freshly; no cached project proof is used.
run([BIN / "lean", "-o", BUILD / "Proofs/Artifacts.olean", "Proofs/Artifacts.lean"], "elaboration.log")
run([BIN / "lean", "-o", BUILD / "Proofs.olean", "Proofs.lean"], "root.log")
bundle = BUILD / "proofs.ndjson"
run([BIN / "leanexport", "Proofs.Artifacts", "--", *TARGETS], "export.log", output=bundle)
summary = audit(bundle)
(BUILD / "audit.json").write_text(json.dumps(summary, indent=2) + "\n")
print("Fresh proofs, axiom whitelist, and literal-to-artifact binding: OK", flush=True)
for checker in ("leanchecker", "leanchecker-paranoid"):
    text = run([BIN / checker, "--from-export", bundle], checker + ".log")
    if "Lean default kernel accepts the solution" not in text:
        raise RuntimeError("missing positive kernel acknowledgement: " + checker)
    print(checker + ": accepts full exported dependency closure", flush=True)
text = nanoda(bundle, "nanoda")
if "no typechecker errors" not in text and "with no errors" not in text:
    raise RuntimeError("missing independent kernel acknowledgement: " + text)
print("Independent Rust kernel Nanoda: accepts full exported dependency closure", flush=True)

# False theorems deliberately injected without elaboration/kernel checking.
for module, theorem in (("ForgedFalse", "forgedFalse"), ("ForgedArithmetic", "forgedArithmetic")):
    run([BIN / "lean", "-o", BUILD / (module + ".olean"), "verification/" + module + ".lean"], module + "-compile.log")
    bad = BUILD / (module + ".ndjson")
    run([BIN / "leanexport", module, "--", theorem], module + "-export.log", output=bad)
    for checker in ("leanchecker", "leanchecker-paranoid"):
        run([BIN / checker, "--from-export", bad], module + "-" + checker + ".log", reject="declaration type mismatch")
    nanoda(bad, module + "-nanoda", reject="assertion failed: self.def_eq")
    print(f"Negative control {theorem}: all three kernel replays REJECT", flush=True)

# Kernel-valid assumptions must still be excluded by the axiom audit.
run([BIN / "lean", "-o", BUILD / "AdmittedFalse.olean", "verification/AdmittedFalse.lean"], "admitted-compile.log")
admitted = BUILD / "admitted.ndjson"
run([BIN / "leanexport", "AdmittedFalse", "--", "admittedFalse"], "admitted-export.log", output=admitted)
try:
    audit(admitted, targets=[], artifacts={})
except RuntimeError as exc:
    if "unapproved axioms" not in str(exc):
        raise
else:
    raise RuntimeError("axiom audit accepted an assumed False")
nanoda(admitted, "admitted-nanoda", reject="unpermitted axiom")
print("Negative control assumed False: axiom audit and Nanoda REJECT", flush=True)

# A proof about the old bytes must not be accepted as about altered bytes.
changed = BUILD / "changed-artifact.txt"
changed.write_bytes(b"0.0\n")
try:
    audit(bundle, artifacts={"Artifacts.edgeBytes": changed})
except RuntimeError as exc:
    if "artifact bytes mismatch" not in str(exc):
        raise
else:
    raise RuntimeError("binding audit accepted different artifact bytes")
print("Negative control altered artifact: binding audit REJECTS", flush=True)

print(run(["Rscript", "verification/replay.R"], "R-replay.log"), end="", flush=True)
print(run(["python3", "verification/replay.py"], "python-replay.log"), end="", flush=True)
files = ["Proofs/Artifacts.lean", "Proofs.lean", "verification/check.py", "check.sh",
         "verification/replay.R", "verification/replay.py", "verification/ForgedFalse.lean",
         "verification/ForgedArithmetic.lean", "verification/AdmittedFalse.lean"]
size = "\n".join(f"{p}: {len(Path(p).read_text().splitlines())} lines, {Path(p).stat().st_size} bytes" for p in files)
(BUILD / "review-size.txt").write_text(size + "\n")
print(size, flush=True)
print("CHECK PASSED: R3 formally REFUTED; R1/R2 reproduced numerically, full conformance UNPROVED.", flush=True)
