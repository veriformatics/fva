#!/usr/bin/env python3
"""Byte bridge and independent Wasmtime replay. No third-party Python modules."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
EXPECTED_HASH = "1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775"


def run(*args):
    result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(f"command failed: {args}\n{result.stdout}\n{result.stderr}")
    return result.stdout


def byte_bridge():
    raw = (ROOT / "lz4-flex.wasm").read_bytes()
    assert len(raw) == 7161
    assert hashlib.sha256(raw).hexdigest() == EXPECTED_HASH
    text = (ROOT / "Proofs/Artifact.lean").read_text()
    literal = re.search(r"def artifact : Array Nat := #\[(.*?)\]", text, re.S)
    assert literal, "artifact literal missing"
    assert re.fullmatch(r"[\d,\s]*", literal[1])
    assert bytes(map(int, re.findall(r"\d+", literal[1]))) == raw
    run("wasm-tools", "validate", "lz4-flex.wasm")
    wat = run("wasm-tools", "print", "lz4-flex.wasm")
    assert '(export "lz4_decompress" (func 7))' in wat
    assert '(export "memory" (memory 0))' in wat
    assert "(memory (;0;) 32 32)" in wat
    assert "(import " not in wat and "(start " not in wat
    assert "(func (;7;) (type 4) (param i32 i32 i32 i32) (result i32)" in wat
    print(f"PASS byte bridge: {len(raw)} bytes, sha256 {EXPECTED_HASH}")


def lean_case_bridge(cases):
    """The Lean literals and native replay must describe identical test cases."""
    text = (ROOT / "Proofs/Cases.lean").read_text()
    for i, c in enumerate(cases):
        output = "none" if c["output"] is None else "some " + str(c["output"])
        literal = (f'  ⟨{json.dumps(c["name"])}, {c["input"]}, {c["cap"]}, '
                   f'{output}, {c["src"]}, {c["dst"]}⟩')
        assert f"def case_{i} : Case :=\n{literal}\n" in text
    expected_list = "def cases : List Case := [" + ", ".join(
        f"case_{i}" for i in range(len(cases))) + "]"
    assert expected_list in text
    assert len(re.findall(r"^def case_\d+ : Case", text, re.M)) == len(cases)
    print(f"PASS case bridge: {len(cases)} identical Lean/native inputs")


def native_replay(cases):
    # All caller bytes start at zero, exactly as in the sparse Lean memory.
    # For each case compare every caller byte outside dst against that initial
    # memory (including src), and compare the successful decoded prefix.
    wat = ['(module',
           ' (import "decoder" "memory" (memory 32 32))',
           ' (import "decoder" "lz4_decompress" '
           '(func $decode (param i32 i32 i32 i32) (result i32)))']
    for i, c in enumerate(cases):
        src, dst, cap = c["src"], c["dst"], c["cap"]
        assert min(src, dst) >= 131072
        assert src + len(c["input"]) <= 2097152 and dst + cap <= 2097152
        assert src + len(c["input"]) <= dst or dst + cap <= src
        expected = -1 if c["output"] is None else len(c["output"])
        data = ''.join(f"\\{b:02x}" for b in c["input"])
        wat += [f' (data $input{i} "{data}")',
                f' (func $case{i} (local $p i32) (local $expected i32)',
                '  (memory.fill (i32.const 131072) (i32.const 0) '
                '(i32.const 1966080))',
                f'  (memory.init $input{i} (i32.const {src}) '
                f'(i32.const 0) (i32.const {len(c["input"])}))',
                f'  (if (i32.ne (call $decode (i32.const {src}) (i32.const {dst}) '
                f'(i32.const {len(c["input"])}) (i32.const {cap})) '
                f'(i32.const {expected})) (then unreachable))']
        if c["output"] is not None:
            for j, b in enumerate(c["output"]):
                wat += [f'  (if (i32.ne (i32.load8_u (i32.const {dst+j})) '
                        f'(i32.const {b})) (then unreachable))']
        # Save the input in a passive data segment, and read it via a scratch
        # area below the caller region. The shipped decoder never uses this
        # area on the paths checked here. This copy happens after the call.
        wat += [f'  (memory.init $input{i} (i32.const 80000) '
                f'(i32.const 0) (i32.const {len(c["input"])}))',
                '  (local.set $p (i32.const 131072))',
                '  (loop $scan',
                f'   (if (i32.or (i32.lt_u (local.get $p) (i32.const {dst})) '
                f'(i32.ge_u (local.get $p) (i32.const {dst+cap})))',
                '    (then',
                '     (local.set $expected (i32.const 0))',
                f'     (if (i32.and (i32.ge_u (local.get $p) (i32.const {src})) '
                f'(i32.lt_u (local.get $p) (i32.const {src+len(c["input"])})))',
                '      (then (local.set $expected (i32.load8_u '
                f'(i32.add (i32.const 80000) (i32.sub (local.get $p) (i32.const {src})))))))',
                '     (if (i32.ne (i32.load8_u (local.get $p)) '
                '(local.get $expected)) (then unreachable))))',
                '   (local.set $p (i32.add (local.get $p) (i32.const 1)))',
                '   (br_if $scan (i32.lt_u (local.get $p) (i32.const 2097152))))',
                ' )']
    wat += [' (func (export "check") (result i32)',
            *[f'  (call $case{i})' for i in range(len(cases))],
            f'  (i32.const {len(cases)}))', ')']
    with tempfile.TemporaryDirectory(prefix="lz4-verification-") as temp:
        path = Path(temp) / "replay.wat"
        path.write_text('\n'.join(wat) + '\n')
        result = run("wasmtime", "-C", "cache=n", "--preload", "decoder=lz4-flex.wasm",
                     "--invoke", "check", str(path))
    assert result.strip() == str(len(cases)), result
    print(f"PASS Wasmtime: {len(cases)} returns/outputs and all caller bytes outside dst")


def main():
    byte_bridge()
    cases = json.loads((ROOT / "verification/cases.json").read_text())
    lean_case_bridge(cases)
    native_replay(cases)


if __name__ == "__main__":
    main()
