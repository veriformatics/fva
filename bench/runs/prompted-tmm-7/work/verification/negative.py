"""Replace a checked theorem's proposition with False, retaining its proof term."""
import json
import subprocess
from pathlib import Path
# The negative control needs only the actual R3 theorem's dependency closure.
src=Path('verification/control.ndjson')
with src.open('w') as out:
    subprocess.run(['lake','env','lean','--run','verification/Export.lean',
                    'Verify.r3_fails'],stdout=out,check=True)
records=[json.loads(l) for l in src.read_text().splitlines()]
names={0:''}
false_expr=None
for r in records:
    if 'in' in r:
        if 'str' in r: names[r['in']]=names[r['str']['pre']]+'.'+r['str']['str']
        elif 'num' in r: names[r['in']]=names[r['num']['pre']]+'.'+str(r['num']['i'])
    if 'const' in r and names[r['const']['name']]=='.False' and not r['const']['us']:
        false_expr=r['ie']
assert false_expr is not None
changed=0
for r in records:
    if 'thm' in r and names[r['thm']['name']]=='.Verify.r3_fails':
        r['thm']['type']=false_expr
        changed+=1
assert changed==1
Path('verification/false.ndjson').write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in records))
print('Negative control: Verify.r3_fails now claims False with its original proof')
