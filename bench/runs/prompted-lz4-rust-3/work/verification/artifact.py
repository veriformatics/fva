#!/usr/bin/env python3
"""Extract function 7 verbatim; fail if the shipped module changes."""
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
WASM = ROOT / 'lz4-flex.wasm'
SHA256 = '1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775'

def uleb(data, p):
    value, shift = 0, 0
    while True:
        b = data[p]
        p += 1
        value |= (b & 127) << shift
        if b < 128:
            return value, p
        shift += 7
        assert shift <= 35

def extract():
    data = WASM.read_bytes()
    assert len(data) == 7161 and hashlib.sha256(data).hexdigest() == SHA256
    assert data[:8] == b'\0asm\x01\0\0\0'
    sections, p = {}, 8
    while p < len(data):
        tag = data[p]
        length, p = uleb(data, p + 1)
        assert p + length <= len(data)
        assert tag not in sections or tag == 0
        sections[tag] = data[p:p+length]
        p += length
    assert 2 not in sections and 8 not in sections  # no imports or start function
    assert sections[7] == bytes.fromhex('03066d656d6f727902000c6c7a345f636f6d707265737300060e6c7a345f6465636f6d70726573730007')
    assert sections[5] == bytes.fromhex('01012020')  # fixed 32-page memory
    code = sections[10]
    count, p = uleb(code, 0)
    bodies = []
    for _ in range(count):
        size, p = uleb(code, p)
        bodies.append(code[p:p+size])
        p += size
    assert p == len(code) and count == 9
    body = bodies[7]
    groups, p = uleb(body, 0)
    locals_ = []
    for _ in range(groups):
        n, p = uleb(body, p)
        locals_ += [body[p]] * n
        p += 1
    assert locals_ == [0x7f] * 17 + [0x7e] * 7
    # Function 7 uses type 4: four i32 parameters, one i32 result.
    assert sections[3] == bytes.fromhex('09000102030100040402')
    return body[p:]

def render():
    code = extract()
    rows = [', '.join(map(str, code[i:i+24])) for i in range(0, len(code), 24)]
    return ('-- Generated verbatim from the SHA-256-pinned Wasm; see verification/artifact.py.\n'
            'namespace Artifact\ndef code : List Nat := [\n  ' + ',\n  '.join(rows) + '\n]\nend Artifact\n')

if __name__ == '__main__':
    import sys
    target = ROOT / 'Proofs/Artifact.lean'
    if sys.argv[1:] == ['--write']:
        target.write_text(render())
    else:
        assert target.read_text() == render(), 'Artifact.lean does not match the shipped bytes'
        print('artifact: SHA-256, ABI, and verbatim decoder bytes match')
