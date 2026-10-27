"""Embed the three complete, unmodified ASCII artifacts as Lean byte lists."""
import json
from pathlib import Path
names = [('countsBytes', 'counts.tsv'), ('edgeBytes', 'edger-factors.txt'),
         ('rnaBytes', 'rnanorm-factors.txt')]
text = '-- Generated from entire files by verification/embed.py; do not edit.\nnamespace Artifact\n'
for name, path in names:
    data = Path(path).read_bytes()
    assert data.isascii() and data.endswith(b'\n')
    text += f'def {name} : List Nat := [{",".join(map(str, data))}]\n'
text += 'end Artifact\n'
Path('Proofs/Artifact.lean').write_text(text)
