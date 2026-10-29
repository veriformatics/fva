#!/usr/bin/env python3
"""Finite Wasmtime checks of the original binary; these are not formal proofs."""
from pathlib import Path
import hashlib
import random
import subprocess
import tempfile

root = Path(__file__).resolve().parent.parent
artifact = (root / 'lz4-flex.wasm').read_bytes()
assert hashlib.sha256(artifact).hexdigest() == \
    '1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775'


def decode(data):
    """Independent-block sequence decoder; omit only the three end restrictions."""
    out, pos = bytearray(), 0
    if not data:
        return None

    def length(base):
        nonlocal pos
        if base == 15:
            while True:
                b = data[pos]
                pos += 1
                base += b
                if b != 255:
                    break
        return base

    try:
        while pos < len(data):
            token = data[pos]
            pos += 1
            literals = length(token >> 4)
            if pos + literals > len(data):
                return None
            out.extend(data[pos:pos + literals])
            pos += literals
            if pos == len(data):
                return bytes(out)
            offset = data[pos] + 256 * data[pos + 1]
            pos += 2
            match = length(token & 15) + 4
            if not 1 <= offset <= len(out):
                return None
            if len(out) + match > 20000:
                return None  # Generated tests never require larger outputs.
            for _ in range(match):
                out.append(out[-offset])
        return bytes(out)
    except IndexError:
        return None


def extension(n):
    return bytes([255] * (n // 255) + [n % 255])


def literals(data):
    return bytes([min(len(data), 15) << 4]) + \
        (extension(len(data) - 15) if len(data) >= 15 else b'') + data


def matched(prefix, offset, count, tail):
    a, b = len(prefix), count - 4
    return bytes([(min(a, 15) << 4) | min(b, 15)]) + \
        (extension(a - 15) if a >= 15 else b'') + prefix + \
        offset.to_bytes(2, 'little') + (extension(b - 15) if b >= 15 else b'') + literals(tail)


rng = random.Random(20261029)
blocks = [b'', b'\0', b'\x10A', b'\0\0\0', b'\0\1\0', b'\xf0', b'\x0f\1\0']
blocks += [bytes([i]) for i in range(256)]
for n in [1, 4, 5, 14, 15, 16, 17, 31, 32, 33, 63, 64, 65, 270, 300]:
    prefix = bytes(rng.randrange(256) for _ in range(n))
    blocks.append(literals(prefix))
    for offset in [1, 2, 3, 4, 8, 16, 32, 64]:
        if offset <= n:
            for count in [4, 7, 18, 19, 20, 32, 33, 64, 65, 300]:
                blocks.append(matched(prefix, offset, count, b'01234567'))
blocks += [bytes(rng.randrange(256) for _ in range(rng.randrange(1, 80))) for _ in range(400)]
for _ in range(400):
    data = bytearray(rng.choice(blocks))
    if data:
        data[rng.randrange(len(data))] = rng.randrange(256)
        blocks.append(bytes(data))


def escaped(data):
    return ''.join('\\%02x' % b for b in data)


with tempfile.TemporaryDirectory(prefix='lz4-regression-') as tmp:
    wast = Path(tmp) / 'tests.wast'
    with wast.open('w') as f:
        f.write('(module $artifact binary "' + escaped(artifact) + '")\n(register "lz4" $artifact)\n')
        f.write('''(module $h
  (import "lz4" "memory" (memory 32 32))
  (func (export "poke") (param $p i32) (param $b i32)
    (i32.store8 (local.get $p) (local.get $b)))
  (func (export "peek") (param $p i32) (result i32)
    (i32.load8_u (local.get $p)))
  (func (export "fill") (param $p i32) (param $n i32)
    (memory.fill (local.get $p) (i32.const 165) (local.get $n))))
''')
        cases = 0
        for data in blocks:
            expected = decode(data)
            size = len(expected) if expected is not None else 0
            for cap in sorted({0, max(0, size - 1), size, max(64, size + 34)}):
                # Alternate layouts, including buffers ending at the memory limit.
                src, dst = (131072, 2097152 - max(cap, 1)) if cases % 2 else (2097152 - max(len(data), 1), 131072)
                assert src + len(data) <= dst or dst + cap <= src
                f.write(f';; case {cases}: input={data.hex()} cap={cap}\n')
                f.write(f'(invoke $h "fill" (i32.const {dst - 1}) (i32.const {cap + 1}))\n')
                if dst + cap < 2097152:
                    f.write(f'(invoke $h "poke" (i32.const {dst + cap}) (i32.const 165))\n')
                for i, b in enumerate(data):
                    f.write(f'(invoke $h "poke" (i32.const {src + i}) (i32.const {b}))\n')
                result = size if expected is not None and size <= cap else -1
                f.write(f'(assert_return (invoke $artifact "lz4_decompress" (i32.const {src}) (i32.const {dst}) (i32.const {len(data)}) (i32.const {cap})) (i32.const {result}))\n')
                if result >= 0:
                    for i, b in enumerate(expected):
                        f.write(f'(assert_return (invoke $h "peek" (i32.const {dst + i})) (i32.const {b}))\n')
                f.write(f'(assert_return (invoke $h "peek" (i32.const {dst - 1})) (i32.const 165))\n')
                if dst + cap < 2097152:
                    f.write(f'(assert_return (invoke $h "peek" (i32.const {dst + cap})) (i32.const 165))\n')
                cases += 1
    subprocess.run(['wasmtime', 'wast', '-C', 'cache=n', str(wast)], check=True, cwd=root)
    print(f'PASS: {cases} finite Wasmtime cases; return values, successful output bytes, adjacent canaries.')
    print('No universal R1/R2/R3 proof; read confinement is not tested.')
