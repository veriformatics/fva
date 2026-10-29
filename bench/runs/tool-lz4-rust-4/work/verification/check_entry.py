#!/usr/bin/env python3
"""Bind entry.rs's prefix to the named export in the exact shipped Wasm.
This tiny binary reader is trusted, not itself proved correct in Verus.
"""
import hashlib
from pathlib import Path
import re

if not __debug__:
    raise SystemExit('Python assertion checks must be enabled')

ROOT = Path(__file__).resolve().parent.parent
WASM = (ROOT / 'lz4-flex.wasm').read_bytes()
assert hashlib.sha256(WASM).hexdigest() == '1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775'
assert WASM[:8] == b'\0asm\x01\0\0\0'


def uleb(data, p):
    value, shift = 0, 0
    while True:
        b = data[p]
        p += 1
        value |= (b & 127) << shift
        if b < 128:
            return value, p
        shift += 7
        assert shift < 35


sections = {}
p = 8
while p < len(WASM):
    tag = WASM[p]
    size, p = uleb(WASM, p + 1)
    end = p + size
    assert end <= len(WASM)
    if tag:
        assert tag not in sections
        sections[tag] = WASM[p:end]
    p = end
assert 2 not in sections, 'function indices assume no imports'
exports = sections[7]
count, p = uleb(exports, 0)
index = None
for _ in range(count):
    length, p = uleb(exports, p)
    name = exports[p:p + length]
    p += length
    kind = exports[p]
    target, p = uleb(exports, p + 1)
    if name == b'lz4_decompress':
        assert kind == 0
        index = target
assert p == len(exports) and index is not None
code = sections[10]
count, p = uleb(code, 0)
assert index < count
body = None
for i in range(count):
    size, p = uleb(code, p)
    if i == index:
        body = code[p:p + size]
    p += size
assert p == len(code)
local_groups, p = uleb(body, 0)
for _ in range(local_groups):
    _, p = uleb(body, p)
    assert body[p] in (0x7f, 0x7e)  # i32 or i64
    p += 1
source = (ROOT / 'verification/entry.rs').read_text()
initializer = re.search(r'pub const PREFIX: \[u8; 10\] = \[([^\]]+)\];', source).group(1)
prefix = bytes(int(word.strip(), 16) for word in initializer.split(','))
assert len(prefix) == 10 and body[p:p + len(prefix)] == prefix
print(f'PASS: export lz4_decompress = function {index}; entry bytes = {prefix.hex()}')
