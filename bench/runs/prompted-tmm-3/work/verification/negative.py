"""Make two well-formed exports claiming false statements with an unchanged proof."""
import json
from pathlib import Path

def records(path):
    return [json.loads(line) for line in Path(path).read_text().splitlines()]

def declarations(rs):
    names = {0: ''}
    out = {}
    for r in rs:
        if 'in' in r:
            n = r.get('str', r.get('num'))
            part = n.get('str', str(n.get('i', '')))
            pre = names[n['pre']]
            names[r['in']] = (pre + '.' if pre else '') + part
        for kind in ('thm', 'def', 'axiom'):
            if kind in r:
                out[names[r[kind]['name']]] = (kind, r[kind])
    return out

def make_negatives():
    rs = records('.verification/controls.ndjson')
    ds = declarations(rs)
    assert ds['NegativeControls.control'][0] == 'thm'
    for target in ('falseEquality', 'falseArithmetic'):
        clone = json.loads(json.dumps(rs))
        cs = declarations(clone)
        cs['NegativeControls.control'][1]['type'] = cs['NegativeControls.' + target][1]['value']
        theorem_record = next(r for r in clone if r.get('thm') is cs['NegativeControls.control'][1])
        clone.remove(theorem_record)
        clone.append(theorem_record)  # the replacement type expressions now precede their use
        path = Path('.verification/' + target + '.ndjson')
        path.write_text(''.join(json.dumps(r) + '\n' for r in clone))
        print('Known false proof fixture:', target, '(original proof, false proposition type)')

if __name__ == '__main__':
    make_negatives()
