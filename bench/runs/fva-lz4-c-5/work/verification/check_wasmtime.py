#!/usr/bin/env python3
"""Replay the finite Lean examples in Wasmtime using the unchanged module bytes.
This is a cross-check of examples, not a proof for all LZ4 inputs.
"""
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
ARTIFACT = ROOT / "lz4-c.wasm"
EXPECTED_SHA256 = "8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6"
CASES = [
    ("empty_zero", 131072, 262144, [0], 0, 0, []),
    ("empty_room", 131072, 262144, [0], 1, 0, []),
    ("one_literal", 131072, 262144, [16, 97], 1, 1, [97]),
    ("extended_literals", 131072, 262144, [240, 0] + [97]*15, 15, 15, [97]*15),
    ("overlap_match", 131072, 262144, [19, 97, 1, 0, 80, 98, 99, 100, 101, 102],
     13, 13, [97]*8 + [98, 99, 100, 101, 102]),
    ("extended_match", 131072, 262144, [31, 97, 1, 0, 0, 80, 98, 99, 100, 101, 102],
     25, 25, [97]*20 + [98, 99, 100, 101, 102]),
    ("zero_offset", 131072, 262144, [19, 97, 0, 0, 80, 98, 99, 100, 101, 102],
     13, 13, [97] + [0]*7 + [98, 99, 100, 101, 102]),
    ("source_at_end", 2097150, 131072, [16, 97], 1, 1, [97]),
    ("destination_at_end", 131072, 2097151, [16, 97], 1, 1, [97]),
    ("reject_no_input", 131072, 262144, [], 1, -1, []),
    ("reject_zero_capacity", 131072, 262144, [16, 97], 0, -1, []),
    ("reject_past_offset", 131072, 262144, [19, 97, 2, 0, 80, 98, 99, 100, 101, 102],
     13, -5, []),
]


def quoted(data):
    return '"' + ''.join(f'\\{b:02x}' for b in data) + '"'


def main():
    artifact = ARTIFACT.read_bytes()
    assert len(artifact) == 8469
    assert hashlib.sha256(artifact).hexdigest() == EXPECTED_SHA256
    script = []
    for i, (name, src, dst, data, capacity, result, output) in enumerate(CASES):
        assert 131072 <= src and src + len(data) <= 2097152
        assert 131072 <= dst and dst + capacity <= 2097152
        assert src + len(data) <= dst or dst + capacity <= src
        script += [f';; {name}', f'(module $m{i} binary {quoted(artifact)})',
                   f'(register "lz4" $m{i})', f'''(module $t{i}
 (import "lz4" "memory" (memory 32 32))
 (import "lz4" "LZ4_decompress_safe" (func $decode (param i32 i32 i32 i32) (result i32)))
 (data (i32.const {dst}) {quoted([165]*capacity)})
 (data (i32.const {src}) {quoted(data)})
 (func (export "run") (result i32)
  i32.const {src} i32.const {dst} i32.const {len(data)} i32.const {capacity} call $decode)
 (func (export "byte") (param i32) (result i32) local.get 0 i32.load8_u))''',
                   f'(assert_return (invoke $t{i} "run") (i32.const {result}))']
        for j, b in enumerate(output):
            script.append(f'(assert_return (invoke $t{i} "byte" (i32.const {dst+j})) (i32.const {b}))')
    with tempfile.TemporaryDirectory(prefix="lz4-verification-") as tmp:
        path = Path(tmp) / "cases.wast"
        path.write_text('\n'.join(script) + '\n')
        env = dict(os.environ, XDG_CACHE_HOME=tmp)
        subprocess.run(["wasmtime", "wast", str(path)], check=True, env=env)
    print(f"PASS: {len(CASES)} cases, unchanged 8469-byte artifact, return values and all expected output bytes")


if __name__ == "__main__":
    main()
