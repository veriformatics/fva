#!/usr/bin/env python3
"""Offline, fail-closed replay of the *partial* results in VERIFICATION.md."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
BUILD = ROOT / ".verification"
TOOLS = Path("/opt/lean/bin")
SHA = "1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775"
TARGETS = ["Results.zero_input", "Results.certified_cases", "Results.cases_valid_buffers"]


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def call(args, *, env=None, output=None, reject=None):
    p = subprocess.run([str(x) for x in args], cwd=ROOT, env=env,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if output:
        Path(output).write_text(p.stdout)
    if reject:
        require(p.returncode != 0 and reject in p.stdout,
                f"negative control did not produce the required type rejection: {args}\n{p.stdout}")
    else:
        require(p.returncode == 0, f"command failed: {args}\n{p.stdout}")
    return p.stdout


def uleb(data, p):
    value, shift = 0, 0
    while True:
        b = data[p]
        p += 1
        value |= (b & 127) << shift
        if b < 128:
            return value, p
        shift += 7
        require(shift <= 35, "bad LEB")


def artifact():
    data = (ROOT / "lz4-flex.wasm").read_bytes()
    require(len(data) == 7161 and hashlib.sha256(data).hexdigest() == SHA,
            "the shipped artifact has changed")
    require(data[:8] == b"\0asm\1\0\0\0", "Wasm header")
    sections, p = {}, 8
    while p < len(data):
        kind = data[p]
        size, p = uleb(data, p + 1)
        require(kind not in sections, "duplicate section")
        sections[kind] = (p, data[p:p + size])
        p += size
    require(p == len(data) and 2 not in sections and 8 not in sections,
            "unexpected imports/start")
    # Resolve the actual export, rather than assuming that source names survive.
    exports, p = sections[7][1], 0
    count, p = uleb(exports, p)
    resolved = {}
    for _ in range(count):
        size, p = uleb(exports, p)
        name = exports[p:p + size].decode("utf-8")
        p += size
        kind, p = exports[p], p + 1
        index, p = uleb(exports, p)
        resolved[name] = (kind, index)
    require(p == len(exports) and resolved["lz4_decompress"] == (0, 7), "export changed")
    require(sections[5][1] == bytes([1, 1, 32, 32]), "memory is not fixed at 32 pages")
    code_offset, code = sections[10]
    count, p = uleb(code, 0)
    bodies = []
    for _ in range(count):
        size, p = uleb(code, p)
        bodies.append((code_offset + p, code[p:p + size]))
        p += size
    offset, body = bodies[resolved["lz4_decompress"][1]]
    require(p == len(code) and offset == 4437 and len(body) == 2000, "code layout changed")
    require(body[:5] == bytes([2, 17, 127, 7, 126]), "local declarations changed")
    generated = (
        "import Proofs.Wasm\n\nnamespace Artifact\n\n"
        "-- Generated verbatim from lz4-flex.wasm, byte offsets [4437,6437).\n"
        "-- check.py pins the full file hash, resolves its export, and compares every byte.\n"
        "def body : List Nat := [\n" + ",\n".join(
            "  " + ", ".join(map(str, body[i:i + 30])) for i in range(0, len(body), 30)) +
        "\n]\n\ndef program : List Wasm.Instr :=\n"
        "  match Wasm.parse 2000 (body.drop 5) with\n"
        "  | some (code, []) => code\n  | _ => []\n\nend Artifact\n")
    require((ROOT / "Proofs/Artifact.lean").read_text() == generated,
            "Lean artifact data or its extraction definition differs")
    call(["wasm-tools", "validate", "lz4-flex.wasm"])
    print(f"artifact: sha256 {SHA}; export 7; exact 2000-byte body matched", flush=True)
    return data


def export(module, names, dest, env=None):
    args = [TOOLS / "leanexport", module, "--", *names]
    return call(args if env else ["lake", "env", *args], env=env, output=dest)


def audit_export(path):
    names, axioms, theorems = {0: ""}, [], []
    for line in path.read_text().splitlines():
        record = json.loads(line)
        if "in" in record:
            if "str" in record:
                n = record["str"]
                names[record["in"]] = ".".join(filter(None, [names[n["pre"]], n["str"]]))
            else:
                n = record["num"]
                names[record["in"]] = f'{names[n["pre"]]}.{n["i"]}'
        if "axiom" in record:
            axioms.append(names[record["axiom"]["name"]])
        if "thm" in record:
            theorems.append(names[record["thm"]["name"]])
    require(set(TARGETS) <= set(theorems), "missing requested theorems")
    require(set(axioms) <= {"propext", "Quot.sound", "Classical.choice"},
            f"unapproved axioms in proof closure: {axioms}")
    print(f"export: all {len(TARGETS)} theorem roots present; axiom declarations {axioms}", flush=True)


def replays(path, label, negative=False):
    commands = [
        ("Lean", [TOOLS / "leanchecker", "--from-export", path], "type mismatch"),
        ("Nanoda", [TOOLS / "nanoda_bin", BUILD / "nanoda.json"], "assertion failed: self.def_eq"),
        ("con-leche", [TOOLS / "con-leche", "--verified", "--jobs=2", path], "type mismatch"),
        ("con-ron", [TOOLS / "con-ron", "--verified", "--jobs=2", path], "type mismatch"),
    ]
    (BUILD / "nanoda.json").write_text(json.dumps({
        "export_file_path": str(path), "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        "unpermitted_axiom_hard_error": True, "nat_extension": True, "string_extension": True,
        "pp_declars": [], "pp_to_stdout": False, "print_success_message": False,
    }))
    for name, command, rejection in commands:
        call(command, output=BUILD / f"{label}-{name}.log", reject=rejection if negative else None)
        print(f"{name}: {'REJECTED known false proof' if negative else 'ACCEPTED proof closure'} ({label})", flush=True)


def negatives():
    for module, name in [("FalseProof", "knownFalse"), ("UnequalProof", "knownUnequal")]:
        call(["lake", "env", "lean", "-R", "verification", "-o", BUILD / f"{module}.olean",
              ROOT / "verification" / f"{module}.lean"])
        env = dict(os.environ, LEAN_PATH=str(BUILD))
        path = BUILD / f"{module}.ndjson"
        export(module, [name], path, env)
        replays(path, module, negative=True)


def escaped(data):
    return '"' + "".join(f"\\{b:02x}" for b in data) + '"'


def runtime(data):
    lines = call(["lake", "env", "lean", "--run", "verification/Emit.lean"]).splitlines()
    cases = []
    for line in lines:
        inp, cap, out = line.split("|")
        parse = lambda s: bytes(map(int, s.split(","))) if s else b""
        cases.append((parse(inp), int(cap), None if out == "-" else parse(out)))
    require(len(cases) == 11, "unexpected case census")
    script = []
    for i, (inp, cap, out) in enumerate(cases):
        # The binary module embedded here is the ENTIRE unchanged shipped file.
        script += [f"(module $d{i} binary {escaped(data)})", f'(register "d{i}" $d{i})',
                   f'(module $h{i} (import "d{i}" "memory" (memory 32 32))',
                   f'  (data $input {escaped(inp)})',
                   '  (func (export "setup")',
                   '    (memory.fill (i32.const 131072) (i32.const 165) (i32.const 1966080))',
                   f'    (memory.init $input (i32.const 131072) (i32.const 0) (i32.const {len(inp)}))))']
        # A separate inspector reads the module's exported memory after the call.
        expected = list(enumerate(inp, 131072))
        if out is not None:
            expected += list(enumerate(out, 262144))
        expected += [(p, 165) for p in list(range(262128, 262144)) +
                     list(range(262144 + cap, 262160 + cap))]
        tests = "\n".join(f"(if (i32.ne (i32.load8_u (i32.const {p})) (i32.const {b})) (then (return (i32.const 0))))"
                          for p, b in expected)
        script += [f'(module $v{i} (import "d{i}" "memory" (memory 32 32))',
                   f' (func (export "inspect") (result i32) {tests} (i32.const 1)))',
                   f'(assert_return (invoke $h{i} "setup"))',
                   f'(assert_return (invoke $d{i} "lz4_decompress" (i32.const 131072) (i32.const 262144) '
                   f'(i32.const {len(inp)}) (i32.const {cap})) (i32.const {len(out) if out is not None else -1}))',
                   f'(assert_return (invoke $v{i} "inspect") (i32.const 1))']
    # Independently exercise the n=0 theorem at the opposite edge of caller memory.
    script += ['(assert_return (invoke $d0 "lz4_decompress" (i32.const 2097151) (i32.const 131072) '
               '(i32.const 0) (i32.const 1966079)) (i32.const -1))']
    path = BUILD / "artifact.wast"
    path.write_text("\n".join(script) + "\n")
    call(["wasmtime", "wast", "-C", "cache=n", path], output=BUILD / "wasmtime.log")
    call(["wast2json", path, "-o", BUILD / "artifact.json"])
    call(["spectest-interp", BUILD / "artifact.json"], output=BUILD / "wabt.log")
    # Negative controls also validate the assertion harness in each runtime.
    bad = BUILD / "false-assertion.wast"
    bad.write_text('(module (func (export "one") (result i32) i32.const 1))\n'
                   '(assert_return (invoke "one") (i32.const 2))\n')
    call(["wasmtime", "wast", "-C", "cache=n", bad], reject="expected")
    call(["wast2json", bad, "-o", BUILD / "false-assertion.json"])
    call(["spectest-interp", BUILD / "false-assertion.json"], reject="expected")
    print("runtimes: Wasmtime and WABT accepted all artifact assertions and rejected 1=2", flush=True)


def census():
    paths = ["Proofs/Wasm.lean", "Proofs/Format.lean", "Proofs/Results.lean", "Proofs.lean",
             "verification/check.py", "verification/Emit.lean", "verification/Audit.lean",
             "verification/FalseProof.lean", "verification/UnequalProof.lean", "Proofs/Artifact.lean"]
    result = {p: {"lines": len((ROOT / p).read_text().splitlines()), "bytes": (ROOT / p).stat().st_size} for p in paths}
    (BUILD / "sizes.json").write_text(json.dumps(result, indent=2) + "\n")
    print("review sizes: .verification/sizes.json (includes generated artifact data)", flush=True)


def main():
    os.chdir(ROOT)
    BUILD.mkdir(exist_ok=True)
    data = artifact()
    # Rebuild local proof sources; never use a previously supplied local .olean.
    local_build = ROOT / ".lake/build"
    if local_build.exists():
        shutil.rmtree(local_build)
    print("building Lean proof terms from source", flush=True)
    call(["lake", "build"], output=BUILD / "build.log")
    audit = call(["lake", "env", "lean", "verification/Audit.lean"], output=BUILD / "axioms.log")
    print(audit.strip(), flush=True)
    path = BUILD / "proofs.ndjson"
    export("Proofs", TARGETS, path)
    audit_export(path)
    replays(path, "proofs")
    negatives()
    runtime(data)
    census()
    print("PASS: partial certificates, artifact replay, and negative controls. R1–R3 remain unproved in general.", flush=True)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError, KeyError, IndexError) as error:
        sys.exit(f"FAIL: {error}")
