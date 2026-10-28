#!/usr/bin/env python3
"""Rebuild, replay, run negative controls, and test the unchanged shipped binary."""
import json
import re
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LOG = ROOT / "verification/logs"
KERNEL = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip()) / "bin"
TARGETS = ["Artifact.zeroCapacity", "Artifact.zeroInput", "Artifact.emptyBlock",
           "Artifact.zeroCapacityConverse"]


def run(label, args, reject=None, contains=None, save=None):
    p = subprocess.run([str(a) for a in args], cwd=ROOT, capture_output=True, text=True)
    output = p.stdout + p.stderr
    (LOG / (label + ".log")).write_text(output)
    if save is not None:
        (ROOT / save).write_text(p.stdout)
    if reject:
        assert p.returncode != 0 and re.search(reject, output), (label, p.returncode, output)
    else:
        assert p.returncode == 0, (label, p.returncode, output)
    if contains:
        assert re.search(contains, output), (label, output)
    print(label + (": rejected as required" if reject else ": PASS"), flush=True)
    return output


def nanoda(label, export, reject=None):
    cfg = {"export_file_path": export, "permitted_axioms": ["propext", "Quot.sound"],
           "unpermitted_axiom_hard_error": True, "nat_extension": True,
           "string_extension": True, "print_success_message": True}
    path = ROOT / "verification" / (label + ".json")
    path.write_text(json.dumps(cfg, indent=2) + "\n")
    run(label, [KERNEL / "nanoda_bin", path], reject=reject,
        contains=None if reject else r"Checked \d+ declarations with no typechecker errors")


def replays(tag, export, negative=False):
    for name in ["leanchecker", "leanchecker-paranoid", "lean4lean"]:
        mode = "--import" if name == "lean4lean" else "--from-export"
        run(tag + "-" + name, [KERNEL / name, mode, export],
            reject=r"declaration type mismatch" if negative else None,
            contains=None if negative else (r"checked \d+ declarations" if name == "lean4lean"
                                            else r"Lean default kernel accepts the solution"))
    nanoda(tag + "-nanoda", export,
           reject=r"assertion failed: self.def_eq" if negative else None)


def review_size():
    theorem_source = (ROOT / "Proofs/EarlyReturn.lean").read_text()
    statements = re.findall(r"^theorem .*? := by", theorem_source, flags=re.M | re.S)
    assert len(statements) == len(TARGETS)
    sizes = {}
    for name in ["Proofs/Semantics.lean", "Proofs/Artifact.lean", "verification/extract.py",
                 "verification/check.py", "verification/cases.py", "verification/runtime.cjs",
                 "verification/Forge.lean", "verification/ForgeEq.lean"]:
        data = (ROOT / name).read_bytes()
        sizes[name] = {"lines": len(data.splitlines()), "bytes": len(data)}
    text = "\n\n".join(s.removesuffix(" := by") for s in statements) + "\n"
    (ROOT / "verification/statements.txt").write_text(text)
    sizes["theorem statements"] = {"lines": len(text.splitlines()), "bytes": len(text.encode())}
    (ROOT / "verification/review-size.json").write_text(json.dumps(sizes, indent=2) + "\n")
    print("Review sizes: verification/review-size.json", flush=True)


def main():
    LOG.mkdir(exist_ok=True)
    run("lean-version", ["lean", "--version"], contains=r"version 4\.35\.0,")
    run("artifact", ["python3", "verification/extract.py", "--check"])
    run("wasm-validation", ["wasm-tools", "validate", "lz4-c.wasm"])
    # Remove only this project's derived build outputs, not the prebuilt dependencies.
    shutil.rmtree(ROOT / ".lake/build", ignore_errors=True)
    run("lean-build", ["lake", "build"])
    run("axioms", ["lake", "env", "lean", "verification/Audit.lean"],
        contains=r"depends on axioms: \[propext, Quot.sound\]")
    run("export", ["lake", "env", KERNEL / "leanexport", "Proofs", "--", *TARGETS],
        save="verification/results.ndjson")
    replays("positive", "verification/results.ndjson")
    for module, target in [("Forge", "Forged.falsehood"), ("ForgeEq", "Forged.wrongEquality")]:
        run(module + "-create", ["lake", "env", "lean", "--root=verification",
                                 f"verification/{module}.lean", "-o",
                                 f".lake/build/lib/lean/{module}.olean"])
        export = f"verification/{module}.ndjson"
        run(module + "-export", ["lake", "env", KERNEL / "leanexport", module, "--", target],
            save=export)
        replays(module, export, negative=True)
    run("cases", ["python3", "verification/cases.py"], contains=r"Generated 1512 concrete executions")
    run("V8", ["node", "verification/runtime.cjs"], contains=r"1512 cases.*PASS")
    run("wasmtime", ["wasmtime", "wast", "-C", "cache=n", "verification/cases.wast"])
    run("wasmtime-false-assertion", ["wasmtime", "wast", "-C", "cache=n", "verification/false.wast"],
        reject=r"(?s)expected\s+0.*actual\s+-1")
    review_size()
    print("CHECK PASSED for the stated partial results. Universal R1, R2, R3: UNPROVED.")


if __name__ == "__main__":
    main()
