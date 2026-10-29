"""Audit exports, and require independent kernels to accept/reject as intended."""
import json
import re
import subprocess
from pathlib import Path

KERNELS = {'con-ron': '/opt/lean/bin/con-ron', 'nanoda': '/opt/lean/bin/nanoda_bin'}
ALLOWED_AXIOMS = {'propext'}

def names_and_audit(path, required):
    names, found, axioms, declarations = {0:''}, set(), [], 0
    for line in path.read_text().splitlines():
        r = json.loads(line)
        if 'in' in r:
            n = r.get('str',r.get('num'))
            names[r['in']] = names[n['pre']] + ('.' if n['pre'] else '') + str(n.get('str',n.get('i')))
        for kind in ['axiom','def','thm','opaque']:
            if kind in r:
                declarations += 1
                name = names[r[kind]['name']]
                found.add(name)
                if kind == 'axiom':
                    axioms.append(name)
                    assert name in ALLOWED_AXIOMS, f'unpermitted axiom: {name}'
    assert required <= found, f'missing roots: {required-found}'
    assert declarations > 0
    return dict(declarations=declarations,axioms=axioms), names

def kernel(kind, export, out, accept):
    if kind == 'con-ron':
        command = [KERNELS[kind],'--verified','--jobs=2',str(export)]
    else:
        config = out/(export.stem+'.nanoda.json')
        config.write_text(json.dumps(dict(export_file_path=str(export.resolve()),
            permitted_axioms=sorted(ALLOWED_AXIOMS),unpermitted_axiom_hard_error=True,
            nat_extension=True,string_extension=True,print_success_message=True,
            pp_declars=[],pp_to_stdout=False)))
        command = [KERNELS[kind],str(config)]
    p = subprocess.run(command,capture_output=True,text=True)
    log = p.stdout + p.stderr
    (out/(export.stem+'.'+kind+'.log')).write_text(log)
    if accept:
        assert p.returncode == 0, log
        if kind == 'con-ron':
            assert re.search(r'accepted [1-9][0-9]* declarations \(--verified\)',log), log
        else:
            assert re.search(r'Checked [1-9][0-9]* declarations with no typechecker errors',log), log
    else:
        assert p.returncode != 0, f'{kind} ACCEPTED A FALSE PROOF: {export}'
        marker = 'type mismatch in theorem' if kind == 'con-ron' else 'assertion failed: self.def_eq'
        assert marker in log, f'{kind} did not reach the intended type error: {log}'
    print(f'{kind}: {"accepted" if accept else "rejected"} {export.name}',flush=True)

def forge_controls(good, out):
    records = [json.loads(s) for s in good.read_text().splitlines()]
    _, names = names_and_audit(good,{'Negative.good','Negative.unequal','Negative.bottom'})
    result = []
    for target in ['unequal','bottom']:
        index = next(k for k,v in names.items() if v == 'Negative.'+target)
        expr = max(r.get('ie',0) for r in records)+1
        changed = []
        for record in records:
            record = json.loads(json.dumps(record))
            if 'thm' in record and names[record['thm']['name']] == 'Negative.good':
                changed.append({'const':{'name':index,'us':[]},'ie':expr})
                record['thm']['type'] = expr
            changed.append(record)
        path = out/('false-'+target+'.ndjson')
        path.write_text(''.join(json.dumps(r)+'\n' for r in changed))
        result.append(path)
    return result
