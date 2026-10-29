#!/usr/bin/env python3
"""Generate Wasmtime assertions embedding the exact shipped module bytes."""
import json
import pathlib
import subprocess
import tempfile
from extract import ROOT, extract

extract()  # digest and interface guard
raw = (ROOT / "lz4-flex.wasm").read_bytes()
escaped = "".join(f"\\{b:02x}" for b in raw)
cases = json.loads((ROOT / "verification/cases.json").read_text())
lines = []
for k, c in enumerate(cases):
    src, dst = c.get("src", 131072), c.get("dst", 262144)
    data = "".join(f"\\{b:02x}" for b in c["input"])
    lines += [f'(module $dut{k} binary "{escaped}")',
              f'(register "dut{k}" $dut{k})',
              '(module',
              f'  (import "dut{k}" "memory" (memory 32 32))',
              f'  (import "dut{k}" "lz4_decompress" (func $decode (param i32 i32 i32 i32) (result i32)))',
              f'  (data (i32.const {src}) "{data}")',
              '  (func (export "run") (result i32)',
              f'    (memory.fill (i32.const {dst}) (i32.const 165) (i32.const {c["cap"]}))',
              f'    (call $decode (i32.const {src}) (i32.const {dst}) (i32.const {len(c["input"])}) (i32.const {c["cap"]})))',
              '  (func (export "byte") (param i32) (result i32) (i32.load8_u (local.get 0)))',
              ')',
              f'(assert_return (invoke "run") (i32.const {c["result"]}))']
    if c["result"] >= 0:
        for i, b in enumerate(c["output"]):
            lines.append(f'(assert_return (invoke "byte" (i32.const {dst+i})) (i32.const {b}))')
with tempfile.TemporaryDirectory(prefix="lz4-verification-") as directory:
    path = pathlib.Path(directory) / "cases.wast"
    path.write_text("\n".join(lines) + "\n")
    subprocess.run(["wasmtime", "wast", "-C", "cache=n", str(path)], cwd=ROOT, check=True)
print(f"PASS: {len(cases)} exact-artifact Wasmtime cases and all successful output bytes")
