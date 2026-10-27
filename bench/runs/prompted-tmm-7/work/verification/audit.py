"""Check export coverage and the axiom allowlist; count the replayed closure."""
from pathlib import Path
from collections import Counter
import json
import sys

def audit(path):
    names={0:''}
    declarations={}
    kinds=Counter()
    axioms=[]
    for line in Path(path).open():
        r=json.loads(line)
        if 'in' in r:
            if 'str' in r: names[r['in']]=(names[r['str']['pre']]+'.'+r['str']['str']).lstrip('.')
            elif 'num' in r: names[r['in']]=names[r['num']['pre']]+'.'+str(r['num']['i'])
        for kind in ['def','thm','opaque','axiom','inductive','quot']:
            if kind not in r: continue
            d=r[kind]
            kinds[kind]+=1
            if 'name' in d:
                name=names[d['name']]
                declarations[name]=kind
                if kind=='axiom': axioms.append(name)
                if kind=='def': assert d['safety']=='safe', ('unsafe declaration',name)
    required=Path('verification/roots.txt').read_text().split()
    assert all(declarations.get(name)=='thm' for name in required), 'missing theorem roots'
    assert set(axioms) <= {'propext','Classical.choice','Quot.sound'}, ('unapproved axioms',axioms)
    assert len(axioms)==len(set(axioms)), 'duplicate axioms'
    result={'declarations':dict(kinds),'axioms':axioms,'roots':len(required),
            'export_bytes':Path(path).stat().st_size}
    print(json.dumps(result,sort_keys=True))
    return result

if __name__=='__main__': audit(sys.argv[1])
