#!/usr/bin/env python3
"""Independent finite observations in wasmtime; these are not universal proofs."""
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile

root = Path(__file__).resolve().parents[1]
artifact = (root / 'lz4-c.wasm').read_bytes()
assert len(artifact) == 8469
assert hashlib.sha256(artifact).hexdigest() == '8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6'
cases = [
    ([0], 0, 0, []),
    ([0], 1, 0, []),
    ([16, 65], 1, 1, [65]),
    ([240, 0] + list(range(15)), 15, 15, list(range(15))),
    ([240, 255, 0] + [65] * 270, 270, 270, [65] * 270),
    ([24, 65, 1, 0, 80, 66, 67, 68, 69, 70], 18, 18,
     [65] * 13 + [66, 67, 68, 69, 70]),
    ([131, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 80, 20, 21, 22, 23, 24],
     20, 20, list(range(8)) + list(range(7)) + list(range(20, 25))),
    ([8, 0, 0, 80, 66, 67, 68, 69, 70], 17, 17,
     [0] * 12 + [66, 67, 68, 69, 70]),
    ([8, 1, 0, 80, 66, 67, 68, 69, 70], 17, -4, []),
    ([240], 32, -2, []),
    ([16], 1, -2, []),
    ([], 1, -1, []),
    ([0, 0, 0, 80, 66, 67, 68, 69, 70], 12, 9,
     [0] * 4 + [66, 67, 68, 69, 70]),
]


def quoted(bs):
    return '"' + ''.join(f'\\{b:02x}' for b in bs) + '"'


script = []
assertions = 0
for index, (source, capacity, result, output) in enumerate(cases):
    assert 131072 + len(source) <= 196600
    assert 196608 + capacity + 8 <= 2097152
    script.extend([
        f'(module $artifact{index} binary {quoted(artifact)})',
        f'(register "artifact" $artifact{index})',
        f'''(module $case{index}
          (import "artifact" "memory" (memory 32 32))
          (import "artifact" "LZ4_decompress_safe"
            (func $decode (param i32 i32 i32 i32) (result i32)))
          (data (i32.const 131072) {quoted(source)})
          (data (i32.const 196600) {quoted([165] * (capacity + 16))})
          (func (export "run") (result i32)
            i32.const 131072 i32.const 196608
            i32.const {len(source)} i32.const {capacity} call $decode)
          (func (export "read") (param i32) (result i32)
            local.get 0 i32.load8_u))''',
        f'(assert_return (invoke $case{index} "run") (i32.const {result}))',
    ])
    assertions += 1
    observations = [(131072, source), (196608, output),
                    (196600, [165] * 8), (196608 + capacity, [165] * 8)]
    for address, values in observations:
        for offset, value in enumerate(values):
            script.append(f'(assert_return (invoke $case{index} "read" '
                          f'(i32.const {address + offset})) (i32.const {value}))')
            assertions += 1
with tempfile.TemporaryDirectory(prefix='lz4-cases-') as tmp:
    path = Path(tmp) / 'cases.wast'
    path.write_text('\n'.join(script) + '\n')
    subprocess.run(['wasmtime', 'wast', str(path)], check=True, cwd=root,
                   env={**os.environ, 'XDG_CACHE_HOME': tmp})
print(f'PASS: {len(cases)} cases, {assertions} runtime assertions on the unchanged artifact')
