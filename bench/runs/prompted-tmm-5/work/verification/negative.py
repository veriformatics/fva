#!/usr/bin/env python3
"""Corrupt well-formed proof exports, without permitting any new axioms."""
import json
import sys
from pathlib import Path
rows=[json.loads(l) for l in Path(sys.argv[1]).read_text().splitlines()]
names={0:''}
for row in rows:
    if 'in' in row and 'str' in row:
        d=row['str'];names[row['in']]='.'.join(filter(None,[names.get(d['pre'],str(d['pre'])),d['str']]))
def decl(n):
    return next((r[k] for r in rows for k in ['thm','def']
                 if k in r and names[r[k]['name']]==n))
for suffix,good,bad in [('false','fixture_true','fixture_false'),('zero_one','fixture_eq','fixture_neq')]:
    changed=json.loads(json.dumps(rows))
    replacement=decl(bad)['value']
    moved=[]
    for row in changed:
        if 'thm' in row and names[row['thm']['name']]==good:
            row['thm']['type']=replacement
            moved.append(row)
    changed=[r for r in changed if r not in moved]+moved
    (Path(sys.argv[2])/f'bad_{suffix}.ndjson').write_text(''.join(json.dumps(r)+'\n' for r in changed))
print('Created True.intro : False and Eq.refl 0 : 0 = 1 negative controls')
