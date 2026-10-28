#!/usr/bin/env python3
"""Strict extraction of function 2 from the pinned, unmodified module."""
import hashlib
from pathlib import Path
import sys

ARTIFACT_HASH = '8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6'
b = Path('lz4-c.wasm').read_bytes()
assert len(b) == 8469 and hashlib.sha256(b).hexdigest() == ARTIFACT_HASH
assert b[:8] == b'\0asm\1\0\0\0'

def leb(data, pos, signed=False):
    value = shift = 0
    while True:
        byte = data[pos]
        pos += 1
        value |= (byte & 127) << shift
        shift += 7
        assert shift <= 35
        if byte < 128:
            if signed and byte & 64:
                value -= 1 << shift
            return value, pos

sections = {}
p = 8
while p < len(b):
    tag = b[p]
    n, p = leb(b, p + 1)
    assert tag not in sections and p + n <= len(b)
    sections[tag] = b[p:p+n]
    p += n
assert p == len(b) and 2 not in sections and 8 not in sections
assert sections[5] == bytes([1, 1, 32, 32])  # one fixed 32-page memory
exports = sections[7]
n, p = leb(exports, 0)
found = {}
for _ in range(n):
    size, p = leb(exports, p)
    name = exports[p:p+size].decode('utf8')
    p += size
    kind = exports[p]
    index, p = leb(exports, p+1)
    found[name] = (kind, index)
assert p == len(exports) and found['LZ4_decompress_safe'] == (0, 2)
code = sections[10]
n, p = leb(code, 0)
assert n == 6
bodies = []
for _ in range(n):
    size, p = leb(code, p)
    bodies.append(code[p:p+size])
    p += size
assert p == len(code)
body = bodies[2]
assert body[:3] == bytes([1, 15, 0x7f])  # 15 i32 locals, four i32 parameters
assert sections[3] == bytes([6, 0, 1, 1, 2, 2, 2])
assert sections[1] == bytes([3, 96, 6, 127,127,127,127,127,127, 1,127,
                           96, 4,127,127,127,127,1,127, 96,3,127,127,127,1,127])
count = 0

def parse(pos):
    global count
    out = []
    while True:
        op = body[pos]
        pos += 1
        count += 1
        if op == 0x0b:
            return out, pos
        if op in (2, 3):
            assert body[pos] == 0x40
            inner, pos = parse(pos+1)
            out.append(('.block' if op == 2 else '.loop') + ' [' + ', '.join(inner) + ']')
            continue
        args = []
        if op in (0x0c, 0x0d, 0x10, 0x20, 0x21, 0x22, 0x23, 0x24):
            v, pos = leb(body, pos)
            args = [v]
        elif 0x28 <= op <= 0x3e:
            a, pos = leb(body, pos)
            offset, pos = leb(body, pos)
            args = [a, offset]
        elif op == 0x41:
            v, pos = leb(body, pos, signed=True)
            args = [v % (1 << 32)]
        else:
            assert op in (0x0f, 0x1a, 0x1b) or 0x45 <= op <= 0x78, hex(op)
        out.append(f'.op {op} [' + ', '.join(map(str, args)) + ']')

instructions, p = parse(3)
assert p == len(body)
output = ('-- Generated from lz4-c.wasm; run verification/extract.py --check.\n'
          'import Proofs.Wasm\nnamespace Artifact\n'
          'def decoder : List Wasm.Ins :=\n  [' + ', '.join(instructions) + ']\nend Artifact\n')
path = Path('Proofs/Artifact.lean')
if '--check' in sys.argv:
    assert path.read_text() == output, 'Artifact.lean differs from binary extraction'
else:
    path.write_text(output)
print(f'Artifact: sha256={ARTIFACT_HASH}, decoder={len(body)} bytes, {count} instructions including ends')
