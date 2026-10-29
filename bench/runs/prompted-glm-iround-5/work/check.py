#!/usr/bin/env python3
"""Offline artifact counterexample, proof replay, and rejection controls."""
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import struct
import subprocess

ROOT = Path(__file__).resolve().parent
os.chdir(ROOT)
OUT = ROOT / ".verification"
OUT.mkdir(exist_ok=True)
ENV = dict(os.environ, XDG_CACHE_HOME=str(OUT / "cache"))
BIN = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip()) / "bin"


def run(args, reject=False, failure_code=None):
    p = subprocess.run(list(map(str, args)), env=ENV, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if (p.returncode != 0) != reject:
        raise RuntimeError(f"Unexpected exit {p.returncode}: {args}\n{p.stdout}")
    if failure_code is not None and p.returncode != failure_code:
        raise RuntimeError(f"Wrong rejection exit {p.returncode}: {args}\n{p.stdout}")
    return p.stdout


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


# Pin the entire artifact, including its export and type sections.
artifact = Path("glm-iround.wasm").read_bytes()
digest = hashlib.sha256(artifact).hexdigest()
require(len(artifact) == 66 and digest ==
        "eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a",
        "Shipped artifact changed")
run(["wasm-tools", "validate", "glm-iround.wasm"])
(OUT / "artifact.wat").write_text(run(["wasm-tools", "print", "glm-iround.wasm"]))

# Check the exact f64.const encoding used to call the original module.
run(["wasm-tools", "parse", "witness.wat", "-o", OUT / "witness.wasm"])
bits = 0x3FDFFFFFFFFFFFFF
encoded = struct.pack("<Q", bits)
require(Path("witness.wat").read_text() ==
        '(module\n  (import "artifact" "iround" (func $iround (param f64) (result i32)))\n'
        '  (func (export "witness") (result i32)\n'
        '    f64.const 0x1.fffffffffffffp-2\n    call $iround))\n',
        "Witness harness changed")
require(b"\x44" + encoded + b"\x10\x00\x0b" in (OUT / "witness.wasm").read_bytes(),
        "Witness binary does not contain the intended f64.const and call")
source = Path("Proofs/Counterexample.lean").read_text()
n, d = [int(re.search(rf"def {name} : Int := (\d+)", source)[1])
        for name in ("numerator", "denominator")]
x = struct.unpack("<d", encoded)[0]
require(x.as_integer_ratio() == (n, d), "Proof input differs from runtime input")
require(((bits >> 52) & 2047) == 1021 and bits >> 63 == 0,
        "Witness must be a positive finite normal binary64")
observed = run(["wasmtime", "run", "--preload", "artifact=glm-iround.wasm",
                "--invoke", "witness", OUT / "witness.wasm"])
require([s for s in observed.splitlines() if re.fullmatch(r"-?\d+", s)] == ["1"],
        f"Artifact did not return 1:\n{observed}")
print(f"Artifact {digest}: iround(0x1.fffffffffffffp-2) = 1")

# Force elaboration from source even if Lake has stale build products.
olean = ROOT / ".lake/build/lib/lean/Proofs/Counterexample.olean"
olean.parent.mkdir(parents=True, exist_ok=True)
compiled = run(["lake", "env", "lean", "-o", olean, "Proofs/Counterexample.lean"])
require("does not depend on any axioms" in compiled, "Unexpected theorem axioms")
export = run(["lake", "env", BIN / "leanexport", "Proofs.Counterexample",
              "--", "Iround.r1_counterexample"])
rows = [json.loads(line) for line in export.splitlines()]
require(not any("axiom" in r for r in rows), "Export has an axiom")
require("thm" in rows[-1], "Expected final theorem record")


def save(name, records):
    path = OUT / (name + ".ndjson")
    path.write_text("".join(json.dumps(r) + "\n" for r in records))
    return path


good = save("proof", rows)
# Forge two well-formed but ill-typed exports: False, and (0 : Nat) = 1.
names = {r["str"]["str"]: r["in"] for r in rows
         if "str" in r and r["str"]["pre"] == 0}


def const(name, universes):
    return next(r["ie"] for r in rows
                if r.get("const") == {"name": names[name], "us": universes})


false_rows = copy.deepcopy(rows)
false_rows[-1]["thm"]["type"] = const("False", [])
false_path = save("false", false_rows)
one_level = next(r["il"] for r in rows if r.get("succ") == 0)
nat_values = {r["natVal"]: r["ie"] for r in rows if "natVal" in r}
next_id = max(r.get("ie", -1) for r in rows) + 1
apps = []
fn = const("Eq", [one_level])
for arg in (const("Nat", []), nat_values["0"], nat_values["1"]):
    app = {"fn": fn, "arg": arg}
    existing = next((r["ie"] for r in rows + apps if r.get("app") == app), None)
    if existing is None:
        apps.append({"ie": next_id, "app": app})
        existing = next_id
        next_id += 1
    fn = existing
last = copy.deepcopy(rows[-1])
last["thm"]["type"] = fn
wrong_eq = save("zero-equals-one", rows[:-1] + apps + [last])

for label, path, reject in [("proof", good, False), ("False", false_path, True),
                             ("0 = 1", wrong_eq, True)]:
    config = OUT / "nanoda.json"
    config.write_text(json.dumps({
        "export_file_path": str(path), "permitted_axioms": [],
        "unpermitted_axiom_hard_error": True, "nat_extension": True,
        "string_extension": True, "print_success_message": True}))
    commands = {
        "Lean": ["lake", "env", BIN / "leanchecker", "--from-export", path],
        "Nanoda": [BIN / "nanoda_bin", config],
        "Con-ron": [BIN / "con-ron", "--verified", path],
    }
    for checker, command in commands.items():
        output = run(command, reject=reject,
                     failure_code={"Lean": 1, "Nanoda": 101, "Con-ron": 1}[checker]
                     if reject else None)
        (OUT / f"{path.stem}-{checker}.log").write_text(output)
        # Con-ron distinguishes rejection (1) from decline/malformed (2/3).
        # Require a semantic rejection diagnostic from every checker.
        expected = ({"Lean": "kernel rejects", "Nanoda":
                     "assertion failed: self.def_eq(u, v)", "Con-ron":
                     "rejected: type mismatch in theorem"}[checker] if reject else
                    {"Lean": "accepts", "Nanoda": "no typechecker errors",
                     "Con-ron": "accepted"}[checker])
        require(expected in output.lower(), f"Missing verdict: {checker}: {output}")
        print(f"{checker}: {'REJECT' if reject else 'ACCEPT'} {label}")

for path in [Path("Proofs/Counterexample.lean"), Path("Proofs.lean"),
             Path("witness.wat"), Path(__file__).resolve()]:
    data = path.read_bytes()
    print(f"Review size: {path.name}: {len(data.splitlines())} lines, {len(data)} bytes")
print("PASS: R1 is false; artifact witness, three kernel replays, and rejection controls checked")
