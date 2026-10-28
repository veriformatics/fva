#!/usr/bin/env python3
"""Build ill-typed exported proof terms, rather than relying on elaboration to reject them."""
from pathlib import Path
import json, sys
rows = [json.loads(s) for s in Path(sys.argv[1]).read_text().splitlines()]
outdir = Path(sys.argv[2]); outdir.mkdir(parents=True, exist_ok=True)
names = {0:''}
for row in rows:
    if 'in' in row:
        x = row.get('str', row.get('num'))
        names[row['in']] = '.'.join(filter(None,[names[x['pre']],str(x.get('str',x.get('i')))]))
assert names[rows[-1]['thm']['name']] == 'Probe.good'
false_id = next(i for i,name in names.items() if name == 'False')
nat_id = next(i for i,name in names.items() if name == 'Nat')
eq_id = next(i for i,name in names.items() if name == 'Eq')
next_e = max(row.get('ie',-1) for row in rows)+1

def output(name, extra, typeid):
    theorem = json.loads(json.dumps(rows[-1]))
    theorem['thm']['type'] = typeid
    (outdir / name).write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in rows[:-1]+extra+[theorem]))

# Reuse existing expression IDs: independent readers require hash-consed input.
exprs = {r['ie']: r for r in rows if 'ie' in r}
existing = {json.dumps({k:v for k,v in r.items() if k!='ie'}, sort_keys=True): i for i,r in exprs.items()}
extra = []
def intern(body):
    key = json.dumps(body,sort_keys=True)
    if key in existing: return existing[key]
    i = next_e + len(extra)
    existing[key] = i
    extra.append(dict(body,ie=i))
    return i

# Reuse the actual checked Eq.refl proof, but claim it proves False.
false_type = intern({'const':{'name':false_id,'us':[]}})
output('false.ndjson',extra,false_type)
# Claim the same proof establishes 0 = 1, at the original Eq universe.
root = rows[-1]['thm']['type']
while 'app' in exprs[root]: root = exprs[root]['app']['fn']
eq_expr = exprs[root]['const']
assert eq_expr['name'] == eq_id
q = intern({'const':eq_expr})
t = intern({'const':{'name':nat_id,'us':[]}})
z = intern({'natVal':'0'})
o = intern({'natVal':'1'})
a = intern({'app':{'fn':q,'arg':t}})
b = intern({'app':{'fn':a,'arg':z}})
c = intern({'app':{'fn':b,'arg':o}})
output('zero_eq_one.ndjson',extra,c)
print('Prepared false proof terms: False and 0 = 1')
