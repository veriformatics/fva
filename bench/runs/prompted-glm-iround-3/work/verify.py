#!/usr/bin/env python3
"""Offline counterexample reproduction, fresh proofs, and kernel controls."""
import collections
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import struct
import subprocess
from fractions import Fraction

ROOT = Path(__file__).resolve().parent
os.chdir(ROOT)
OUT = ROOT / ".verification"
OUT.mkdir(exist_ok=True)
OLEANS = OUT / "olean"
(OLEANS / "Proofs").mkdir(parents=True, exist_ok=True)
ENV = dict(os.environ)
ENV["LEAN_PATH"] = str(OLEANS) + os.pathsep + ENV.get("LEAN_PATH", "")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def run(command, label, expected=0):
    result = subprocess.run(list(map(str, command)), env=ENV, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    (OUT / (label + ".log")).write_text(result.stdout + result.stderr)
    require(result.returncode == expected,
            f"{label}: expected exit {expected}, got {result.returncode}\n"
            + result.stdout[-2000:] + result.stderr[-2000:])
    return result.stdout


# Exact equality, rather than just a digest, binds this run to the shipped bytes.
artifact = Path("glm-iround.wasm").read_bytes()
require(artifact == bytes.fromhex(
    "0061736d0100000001060160017c017f030201000503010001071302066d"
    "656d6f727902000669726f756e6400000a12011000200044000000000000"
    "e03fa0fc020b"), "Artifact bytes changed")
print(f"Artifact: {len(artifact)} bytes, sha256 {hashlib.sha256(artifact).hexdigest()}")
run(["wasm-tools", "validate", "glm-iround.wasm"], "wasm-validate")
run(["wasm-tools", "print", "glm-iround.wasm"], "artifact-disassembly")

source = Path("Proofs/Counterexample.lean").read_text()
constants = dict(re.findall(r"^def (bits|p|q) : Nat := (0x[0-9a-f]+|[0-9]+)$",
                            source, re.MULTILINE))
require(set(constants) == {"bits", "p", "q"}, "Missing literal witness constants")
bits, p, q = (int(constants[key], 0) for key in ("bits", "p", "q"))
# Decode IEEE binary64 independently of the Lean arithmetic certificate.
require(bits >> 63 == 0 and 0 < (bits >> 52) % 2048 < 2047,
        "Input must be a positive finite normal binary64")
x = struct.unpack(">d", bits.to_bytes(8, "big"))[0]
require(Fraction.from_float(x) == Fraction(p, q), "Bits/rational mismatch")
require(0 < p < q and p <= 2147483647 * q and p < q - p,
        "Counterexample arithmetic mismatch")
harness = ('(module\n'
           '  (import "subject" "iround" (func $iround (param f64) (result i32)))\n'
           '  (func (export "counterexample") (result i32)\n'
           f'    i64.const 0x{bits:x}\n'
           '    f64.reinterpret_i64\n'
           '    call $iround))\n')
require(Path("counterexample.wat").read_text() == harness, "Harness changed")
run(["wasm-tools", "parse", "counterexample.wat", "-o", OUT / "harness.wasm"],
    "harness-parse")
result = run(["wasmtime", "run", "-C", "cache=n", "--preload",
              "subject=glm-iround.wasm", "--invoke", "counterexample",
              OUT / "harness.wasm"], "artifact-execution")
require(result.strip() == "1", f"Expected counterexample result 1, got {result!r}")
print(f"R1 FAILS: bits=0x{bits:x}, x={p}/{q}, actual result=1; 0 is closer.")

bindir = Path(run(["lean", "--print-prefix"], "lean-prefix").strip()) / "bin"
# Compile every proof from source into a separate search path on every run.
run(["lean", "-o", OLEANS / "Proofs/Counterexample.olean",
     "Proofs/Counterexample.lean"], "compile-proof")
exports = run([bindir / "leanexport", "Proofs.Counterexample", "--",
               "Verification.binary64_encoding", "Verification.counterexample_arithmetic"],
              "export-proof")
certificate = OUT / "certificate.ndjson"
certificate.write_text(exports)
records = [json.loads(line) for line in exports.splitlines()]
require(not any("axiom" in record for record in records), "Unexpected axiom")


def names_in(records):
    names = {0: ""}
    for record in records:
        if "in" in record:
            node = record.get("str", record.get("num"))
            leaf = node["str"] if "str" in node else str(node["i"])
            names[record["in"]] = ".".join(filter(None, (names[node["pre"]], leaf)))
    return names


names = names_in(records)
theorems = {names[r["thm"]["name"]] for r in records if "thm" in r}
require({"Verification.binary64_encoding", "Verification.counterexample_arithmetic"}
        <= theorems, "The required theorems were not exported")
counts = collections.Counter(key for r in records for key in
                             ("def", "thm", "inductive", "opaque", "quot", "axiom")
                             if key in r)
inventory = []
for record in records:
    for kind in ("def", "thm", "axiom", "opaque", "quot"):
        if kind in record:
            inventory.append(f"{kind}: {names[record[kind]['name']]}")
    if "inductive" in record:
        for kind in ("types", "ctors", "recs"):
            inventory.extend(f"{kind}: {names[item['name']]}"
                             for item in record["inductive"][kind])
(OUT / "dependency-declarations.txt").write_text("\n".join(sorted(inventory)) + "\n")
print(f"Proof dependency records: {dict(counts)}; {len(exports.encode())} bytes; no axioms.")

checkers = [
    ("lean", [bindir / "leanchecker", "--from-export"]),
    ("lean4lean", [bindir / "lean4lean", "--import"]),
    ("con-ron", [bindir / "con-ron", "--verified", "--jobs=2"]),
]


def replay(path, label, expected):
    for name, command in checkers:
        log = label + "-" + name
        run(command + [path], log, expected)
        if expected == 1:
            diagnostic = (OUT / (log + ".log")).read_text()
            require("type mismatch" in diagnostic and "KernelControl.reflexivity" in diagnostic,
                    f"{log}: failed without diagnosing the forged theorem's type mismatch")
        print(f"{name}: {label} {'ACCEPTED' if expected == 0 else 'REJECTED (exit 1)'}")


replay(certificate, "certificate", 0)
# Start with a valid theorem, then change ONLY its type, retaining its proof.
# This bypasses the elaborator and tests the actual kernel replay paths.
(OUT / "KernelControl.lean").write_text("theorem KernelControl.reflexivity : (0 : Nat) = 0 := rfl\n")
run(["lean", "-o", OLEANS / "KernelControl.olean", OUT / "KernelControl.lean"],
    "compile-control")
control = run([bindir / "leanexport", "KernelControl", "--", "KernelControl.reflexivity", "False"],
              "export-control")
good = OUT / "control-valid.ndjson"
good.write_text(control)
replay(good, "valid-control", 0)
control_records = [json.loads(line) for line in control.splitlines()]
control_names = names_in(control_records)
theorem = next(r for r in control_records
               if "thm" in r and control_names[r["thm"]["name"]] == "KernelControl.reflexivity")
expressions = {r["ie"]: r for r in control_records if "ie" in r}
next_expr = max(expressions) + 1
false_name = next(n for n, name in control_names.items() if name == "False")
for label in ("false", "zero-equals-one"):
    bad = [copy.deepcopy(r) for r in control_records if r is not theorem]
    claim = copy.deepcopy(theorem)
    if label == "false":
        bad.append({"ie": next_expr, "const": {"name": false_name, "us": []}})
        claim["thm"]["type"] = next_expr
    else:
        # Eq Nat 0 0 is an application whose final argument is its RHS.
        application = expressions[theorem["thm"]["type"]]["app"]
        bad.append({"ie": next_expr, "natVal": "1"})
        bad.append({"ie": next_expr + 1,
                    "app": {"fn": application["fn"], "arg": next_expr}})
        claim["thm"]["type"] = next_expr + 1
    bad.append(claim)
    path = OUT / ("control-" + label + ".ndjson")
    path.write_text("".join(json.dumps(r, separators=(",", ":")) + "\n" for r in bad))
    replay(path, label, 1)

for path in ("Proofs/Counterexample.lean", "counterexample.wat", "verify.py", "check.sh"):
    data = Path(path).read_bytes()
    print(f"Review size {path}: {len(data.splitlines())} lines, {len(data)} bytes")
print("PASS: R1 counterexample reproduced; fresh proofs accepted by 3 kernels; "
      "both false proofs rejected by all 3. Logs: .verification/")
