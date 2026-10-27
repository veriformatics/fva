"""Check byte identities and replay-to-proof-mask correspondence.

This script does not claim to formally verify R, numpy, or the dependency shims.
"""
from pathlib import Path
from fractions import Fraction
import ast
import hashlib
import json
import subprocess
import sys

from replay import replay


def main():
    for line in Path('verification/SHA256SUMS').read_text().splitlines():
        expected, name = line.split('  ', 1)
        actual = hashlib.sha256(Path(name).read_bytes()).hexdigest()
        assert actual == expected, f'byte identity failed: {name}'
    print('All shipped input, artifact, source, and documentation byte identities passed.')
    masks = json.loads(Path('verification/masks.json').read_text())
    data = Path('Proofs/Data.lean').read_text()
    for name, key in [('ideal','ideal'),('edge','edgeR'),('rna','RNAnorm')]:
        witness = data.split(f'def {name}Masks : List (List ℕ) := ',1)[1].splitlines()[0]
        assert ast.literal_eval(witness) == masks[key], name
    x = [list(map(int, l.split('\t'))) for l in Path('counts.tsv').read_text().splitlines()]
    for j in range(7):
        inds = [k for k,r in enumerate(x) if r[j] and r[3]]
        ratios = [Fraction(x[k][j], x[k][3]) for k in inds]
        products = [x[k][j]*x[k][3] for k in inds]
        def twice_rank(vs, v):
            return 2*sum(w<v for w in vs)+sum(w==v for w in vs)+1
        n = len(inds)
        exact = [k for k,r,p in zip(inds,ratios,products)
                 if 2*(n*3//10+1)<=twice_rank(ratios,r)<=2*(n-n*3//10)
                 and 2*(n//20+1)<=twice_rank(products,p)<=2*(n-n//20)]
        assert exact == masks['ideal'][j]
    out = subprocess.check_output(['Rscript','verification/replay.R'], text=True)
    observed = [list(map(int,l.split(','))) for l in out.splitlines()]
    assert observed == masks['edgeR']
    print('edgeR shipped source: factors reproduced byte for byte; masks match Lean data.')
    values, observed = replay()
    assert observed == masks['RNAnorm']
    print('RNAnorm shipped class methods with dependency shims: abs error < 2e-15; masks match Lean data.')
    print('Selected gene counts:')
    for name in masks:
        print(' ',name,[len(a) for a in masks[name]])
    edge = [Fraction(s) for s in Path('edger-factors.txt').read_text().splitlines()]
    rna = [Fraction(s) for s in Path('rnanorm-factors.txt').read_text().splitlines()]
    assert all(abs(a-b)>Fraction(1,10**10) for a,b in zip(edge,rna))
    print('R3 counterexample differences:',[float(abs(a-b)) for a,b in zip(edge,rna)])
    print('All replay checks passed. Run lake build and the Lean axiom audit for the formal results.')


if __name__ == '__main__':
    main()
