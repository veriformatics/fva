"""Byte binding and grammar checks for the files embedded in the Lean statements."""
import hashlib
import json
import re
from fractions import Fraction
from pathlib import Path

manifest = json.loads(Path('Verification/artifacts.json').read_text())
for name, expected in manifest.items():
    data = Path(name).read_bytes()
    assert len(data) == expected['bytes'], name
    assert hashlib.sha256(data).hexdigest() == expected['sha256'], name
matrix = Path('counts.tsv').read_bytes()
assert re.fullmatch(rb'(?:[0-9]+(?:\t[0-9]+){6}\n){454}', matrix)
for name in ['edger-factors.txt', 'rnanorm-factors.txt']:
    data = Path(name).read_bytes()
    assert re.fullmatch(rb'(?:[0-9]+\.[0-9]+\n){7}', data), name
print('PASS: all 12 shipped files match their recorded bytes; matrix/factor grammars are valid')
e = [Fraction(v) for v in Path('edger-factors.txt').read_text().splitlines()]
r = [Fraction(v) for v in Path('rnanorm-factors.txt').read_text().splitlines()]
assert abs(e[0] - r[0]) > Fraction(9, 1000)
print('PASS: independent exact-decimal check of R3; sample 1 difference =', abs(e[0]-r[0]))
