#!/usr/bin/env python3
"""Embed exact artifact bytes, without translating its implementation."""
from pathlib import Path
import hashlib
p = Path('lz4-c.wasm').read_bytes()
assert len(p) == 8469
assert hashlib.sha256(p).hexdigest() == '8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6'
s = '-- Generated from lz4-c.wasm by verification/embed.py.\nset_option maxRecDepth 4096\nnamespace Artifact\n'
chunks = [p[i:i+256] for i in range(0,len(p),256)]
for i, chunk in enumerate(chunks):
    s += f'def chunk{i} : List Nat := [\n'
    s += ',\n'.join('  '+', '.join(map(str,chunk[j:j+24])) for j in range(0,len(chunk),24))
    s += '\n]\n'
s += 'def chunks : List (List Nat) := [' + ', '.join(f'chunk{i}' for i in range(len(chunks))) + ']\n'
s += 'def byteAt (a : Nat) : Option Nat := do\n  let c ← chunks[a / 256]?\n  c[a % 256]?\n'
s += 'end Artifact\n'
import sys
if '--check' in sys.argv:
    assert Path('Proofs/Bytes.lean').read_text() == s, 'generated file differs: Proofs/Bytes.lean'
else:
    Path('Proofs/Bytes.lean').write_text(s)
