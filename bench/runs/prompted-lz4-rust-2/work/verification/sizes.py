#!/usr/bin/env python3
"""Report custom review surface and the full exported dependency closure."""
import collections, json, pathlib
spec = ['Proofs/Wasm.lean', 'Proofs/Format.lean', 'Proofs/Results.lean']
bridge = ['verification/extract.py', 'verification/check.sh', 'verification/exports.py']
support = ['verification/cases.py', 'verification/make_wast.py', 'verification/runtime.js',
           'verification/sizes.py', 'Proofs/Calibration.lean', 'Proofs.lean']
for label, paths in [('Custom semantics and statements',spec), ('Artifact bridge and checking driver',bridge),
                     ('Additional generation/cross-check code',support),
                     ('Generated instruction data and concrete statements',['Proofs/Artifact.lean','Proofs/Cases.lean']+
                     [str(p) for p in sorted(pathlib.Path('Proofs/Concrete').glob('*.lean'))])]:
    lines = size = 0
    for name in paths:
        data = pathlib.Path(name).read_bytes()
        lines += data.count(b'\n'); size += len(data)
    print(f'{label}: {lines} lines, {size} bytes')
p = pathlib.Path('verification/.build/proofs.ndjson')
if p.exists():
    counts = collections.Counter()
    for line in p.open():
        r = json.loads(line)
        for k in ['def','thm','opaque','axiom','inductive','recursor','quot']:
            if k in r: counts[k] += 1
    print('Full exported dependency closure:', dict(counts), f'; {p.stat().st_size} bytes')
