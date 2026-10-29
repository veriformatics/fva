#!/usr/bin/env python3
"""Axiom/target audit and deliberate invalid proof fixtures for all replay kernels."""
import json, pathlib, sys
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
def audit(path, targets, retain=False):
    rs,ns,components = [],{0:''},{0:()}
    decls, axioms, theorems = [], [], []
    for line in pathlib.Path(path).open():
        r = json.loads(line)
        if retain: rs.append(r)
        if 'in' in r:
            v = r.get('str', r.get('num'))
            pre = ns[v['pre']]
            part = v.get('str', str(v.get('i')))
            ns[r['in']] = (pre+'.' if pre else '')+part
            components[r['in']] = components[v['pre']] + ((v['str'] if 'str' in v else v['i']),)
        for kind in ['def','thm','opaque','axiom','inductive','quot']:
            if kind not in r:
                continue
            d = r[kind]
            if 'name' in d:
                name = ns[d['name']]
                decls.append(name)
                if kind == 'axiom':
                    assert components[d['name']] in {tuple(a.split('.')) for a in allowed}, f'Forbidden axiom: {name}'
                    axioms.append(name)
                if kind == 'thm':
                    theorems.append(components[d['name']])
    assert {tuple(t.split('.')) for t in targets} <= set(theorems), 'Missing required result'
    print(f'Audit: {len(decls)} named declarations, {len(targets)} required theorems; axioms: {axioms}')
    return rs,ns
if sys.argv[1] == 'audit':
    audit(sys.argv[2], ['Verification.empty_input']+[f'Verification.checked{i}' for i in range(38)])
elif sys.argv[1] == 'negative':
    rs,ns = audit(sys.argv[2], ['Calibration.truth','Calibration.arithmetic'], retain=True)
    byexpr = {r['ie']:r for r in rs if 'ie' in r}
    false = next(r['def']['value'] for r in rs if 'def' in r and ns[r['def']['name']]=='Calibration.falseType')
    folder = pathlib.Path(sys.argv[3])
    for target in ['truth','arithmetic']:
        records = json.loads(json.dumps(rs))
        record = next(r for r in records if 'thm' in r and ns[r['thm']['name']]=='Calibration.'+target)
        if target == 'truth':
            record['thm']['type'] = false
        else:
            # Copy the outer Eq application, changing just its right side to 5.
            old = byexpr[record['thm']['type']]['app']
            n = max(byexpr)+1
            records += [{'ie':n, 'natVal':'5'},
                        {'ie':n+1, 'app':{'fn':old['fn'], 'arg':n}}]
            record['thm']['type'] = n+1
        records.remove(record)
        records.append(record)  # All dependencies precede the deliberately ill-typed theorem.
        (folder/(target+'-false.ndjson')).write_text(''.join(json.dumps(r)+'\n' for r in records))
    print('Negative fixtures: True.intro : False; proof of 2+2=4 offered as proof of 2+2=5')
else:
    raise SystemExit('unknown mode')
