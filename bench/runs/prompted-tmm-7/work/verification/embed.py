"""Byte-preserving ASCII embedding. No algorithm or numerical results here."""
from pathlib import Path
import json
import sys
paths = ['counts.tsv', 'edger-factors.txt', 'rnanorm-factors.txt']
names = ['countsBytes', 'edgeBytes', 'rnaBytes']
out = 'namespace Verify\n'
for path, name in zip(paths, names):
    raw = Path(path).read_bytes()
    assert raw.isascii()
    out += f'def {name} : List Nat := {list(raw)}\n'
out += 'end Verify\n'
path = Path('Proofs/Artifacts.lean')
if '--check' in sys.argv:
    assert path.read_bytes() == out.encode(), 'artifact bytes differ from their Lean embedding'
else:
    path.write_text(out)
