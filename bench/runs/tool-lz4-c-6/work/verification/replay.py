"""Execute fixed examples against an exact binary embedded in a WAST file.
This is regression testing, not a universal proof.
"""
from pathlib import Path
import hashlib
import subprocess

root = Path(__file__).resolve().parent.parent
blob = (root / 'lz4-c.wasm').read_bytes()
assert hashlib.sha256(blob).hexdigest() == '8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6'


def length_bytes(n):
    return bytes([255] * (n // 255) + [n % 255])


def literals(data):
    n = len(data)
    return bytes([min(n, 15) << 4]) + (length_bytes(n - 15) if n >= 15 else b'') + data


cases = []
for n in [*range(15), 15, 16, 269, 270, 271, 525, 526]:
    data = bytes((i * 37 + 11) % 256 for i in range(n))
    cases.append((f'literals_{n}', literals(data), max(1, n), data, n))
    if n:
        cases.append((f'too_small_{n}', literals(data), n - 1, b'', None))
cases += [('empty_capacity', b'\0', 0, b'', 0),
          ('empty_source', b'', 32, b'', -1),
          ('zero_capacity_nonzero_token', b'\1', 0, b'', -1),
          ('low_nibble_ignored', b'\x0f', 1, b'', 0)]
for offset in [0, 1]:
    for n in [7, 18, 19, 20, 274, 529]:
        # One literal, a match, then exactly five final literals.
        token = 0x10 | min(n - 4, 15)
        block = bytes([token, 65, offset, 0])
        if n >= 19:
            block += length_bytes(n - 19)
        block += b'\x50abcde'
        expected = b'A' + (b'A' if offset else b'\0') * n + b'abcde'
        cases.append((f'offset_{offset}_match_{n}', block, len(expected), expected, len(expected)))
cases += [('past_start', b'\x10A\x02\x00\x50abcde', 32, b'', None),
          ('truncated_literal_extension', b'\xf0\xff', 600, b'', None),
          ('truncated_offset', b'\x10A\x01', 32, b'', None)]

out = ['(module $lz4 binary "' + ''.join(f'\\{b:02x}' for b in blob) + '")',
       '(register "lz4" $lz4)',
       '(module $h',
       ' (import "lz4" "memory" (memory 32 32))',
       ' (import "lz4" "LZ4_decompress_safe" (func $decode (param i32 i32 i32 i32) (result i32)))']
count = 0
for name, data, cap, expected, result in cases:
    for s, d in [(131072, 1048576), (2097152-len(data), 131072)]:
        # Empty ranges can start at the last in-range address.
        s = min(s, 2097151)
        func = f'{name}_{count}'
        count += 1
        out += [f' (func (export "{func}") (result i32) (local $r i32)']
        for i, b in enumerate(data):
            out.append(f'  (i32.store8 (i32.const {s+i}) (i32.const {b}))')
        for i in range(-1, cap + 1):
            out.append(f'  (i32.store8 (i32.const {d+i}) (i32.const 165))')
        out.append(f'  (local.set $r (call $decode (i32.const {s}) (i32.const {d}) (i32.const {len(data)}) (i32.const {cap})))')
        if result is None:
            cond = '(i32.ge_s (local.get $r) (i32.const 0))'
        else:
            cond = f'(i32.ne (local.get $r) (i32.const {result}))'
        out.append(f'  (if {cond} (then unreachable))')
        for i, b in enumerate(expected):
            out.append(f'  (if (i32.ne (i32.load8_u (i32.const {d+i})) (i32.const {b})) (then unreachable))')
        for p in [d-1, d+cap]:
            out.append(f'  (if (i32.ne (i32.load8_u (i32.const {p})) (i32.const 165)) (then unreachable))')
        out.append('  (i32.const 1))')
out.append(')')
for i, (name, *_rest) in enumerate(cases):
    for j in range(2):
        index = 2*i+j
        out.append(f'(assert_return (invoke $h "{name}_{index}") (i32.const 1))')
path = root / 'verification/replay.wast'
path.write_text('\n'.join(out) + '\n')
subprocess.run(['wasmtime', 'wast', '-C', 'cache=n', str(path)], check=True)
print(f'Exact-artifact regression: {count} invocations passed (return, output, two guard bytes).')
