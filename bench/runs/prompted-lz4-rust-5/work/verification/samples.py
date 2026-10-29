#!/usr/bin/env python3
"""Render the explicit sample data; statements are in Proofs/Cases.lean."""
import json
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
cases = json.loads((ROOT/'verification/cases.json').read_text())
lines = ['import Init', '', 'namespace Samples', 'structure Case where',
         '  input : List Nat', '  cap : Nat', '  output : List Nat',
         '  result : Nat', '  fuel : Nat', '  deriving DecidableEq, Repr', '']
for c in cases:
    lines.append('def '+c['name']+' : Case := ⟨'+', '.join([
        str(c['input']),str(c['cap']),str(c['output']),
        str(c['result'] % (1 << 32)),str(c['fuel'])])+'⟩')
lines += ['', 'def all : List Case := ['+', '.join(c['name'] for c in cases)+']',
          'end Samples', '']
result = '\n'.join(lines)
path = ROOT/'Proofs/Samples.lean'
if '--check' in sys.argv:
    assert path.read_text() == result
else:
    path.write_text(result)
print(f'sample data: {len(cases)} cases')
