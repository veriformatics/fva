#!/usr/bin/env python3
"""One-command replay, including deliberate bad proofs. No network is used."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

os.chdir(Path(__file__).resolve().parent.parent)
gen = Path('verification/generated')
gen.mkdir(exist_ok=True)
kernels = [('/opt/lean/bin/leanchecker-paranoid','--from-export'),
           ('/opt/lean/bin/lean4lean','--import')]
roots = ['Artifact.lift_exact','Artifact.ends_exact','Verification.empty_input','Verification.corpus']

def command(args, logfile=None, expected=True):
    result = subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    if logfile: (gen/logfile).write_text(result.stdout)
    if expected and result.returncode:
        print(result.stdout)
        raise RuntimeError(f'Command failed ({result.returncode}): {args}')
    return result

def audit(path, required):
    names, declarations, axioms = {0:''}, {}, []
    counts = {}
    for line in path.read_text().splitlines():
        obj = json.loads(line)
        if 'in' in obj:
            if 'str' in obj:
                data = obj['str']; prefix = names[data['pre']]
                names[obj['in']] = (prefix+'.' if prefix else '')+data['str']
            elif 'num' in obj:
                data = obj['num']; prefix = names[data['pre']]
                names[obj['in']] = (prefix+'.' if prefix else '')+str(data['i'])
        for key in ('axiom','def','thm','opaque','inductive','quot'):
            if key in obj:
                counts[key] = counts.get(key,0)+1
                data = obj[key]
                if isinstance(data,dict) and 'name' in data:
                    name = names[data['name']]; declarations[name] = key
                    assert name != 'sorryAx', 'sorry dependency'
                    if key == 'axiom': axioms.append(name)
    assert set(axioms) <= {'propext'}, f'Unexpected axioms: {axioms}'
    for root in required: assert declarations.get(root) == 'thm', f'Missing theorem {root}'
    return {'bytes':path.stat().st_size,'lines':sum(1 for _ in path.open()),'declarations':counts,'axioms':axioms}

print('Pin and lift the shipped artifact',flush=True)
before = Path('Proofs/Artifact.lean').read_bytes()
print(command(['python3','verification/lift.py']).stdout,end='')
assert before == Path('Proofs/Artifact.lean').read_bytes(), 'Generated lift was stale; inspect and rerun'
command(['wasm-tools','validate','lz4-flex.wasm'])
assert '4.35.0' in command(['lake','env','lean','--version']).stdout
# Rebuild the local proof modules, rather than accepting previously cached oleans.
for folder in ('.lake/build/lib/lean/Proofs','.lake/build/ir/Proofs'):
    if Path(folder).exists(): shutil.rmtree(folder)
for path in Path('.lake/build/lib/lean').glob('Proofs.*'): path.unlink()
print('Rebuild computational proofs in Lean (no native_decide)',flush=True)
build = command(['lake','build'], 'build.log')
print(build.stdout,end='')
export = command(['lake','env','/opt/lean/bin/leanexport','Proofs','--']+roots)
positive = gen/'proofs.ndjson'; positive.write_text(export.stdout)
stats = audit(positive,roots)
(gen/'closure.json').write_text(json.dumps(stats,indent=2)+'\n')
for kernel, flag in kernels:
    result = command([kernel,flag,str(positive)],Path(kernel).name+'.log')
    assert 'accepts the solution' in result.stdout or re.search(r'checked [1-9][0-9]* declarations',result.stdout)
    print(Path(kernel).name+': '+result.stdout.strip(),flush=True)
print('Try forged proofs: False from True.intro; 0=1 from Eq.refl 0',flush=True)
false_olean = Path('.lake/build/lib/lean/verification/FalseProofs.olean')
false_olean.parent.mkdir(exist_ok=True)
command(['lake','env','lean','-o',str(false_olean),'verification/FalseProofs.lean'])
for name in ('badFalse','badEquality'):
    bad = gen/(name+'.ndjson')
    bad.write_text(command(['lake','env','/opt/lean/bin/leanexport','verification.FalseProofs','--',name]).stdout)
    # The false declaration must actually be in the exported file.
    assert name in bad.read_text() and '"thm"' in bad.read_text()
    for kernel, flag in kernels:
        result = command([kernel,flag,str(bad)],name+'.'+Path(kernel).name+'.log',expected=False)
        assert result.returncode != 0, f'{kernel} accepted {name}'
        assert 'declaration type mismatch' in result.stdout and name in result.stdout, result.stdout
        print(Path(kernel).name+': rejected '+name,flush=True)
print(command(['python3','verification/runtime.py'],'runtime.log').stdout,end='')
files = ['Proofs/Machine.lean','Proofs/Claims.lean','verification/lift.py',
         'verification/check.py','verification/Emit.lean','verification/runtime.py',
         'verification/FalseProofs.lean','Proofs.lean','Proofs/Artifact.lean']
sizes = {p:{'lines':len(Path(p).read_text().splitlines()),'bytes':Path(p).stat().st_size} for p in files}
(gen/'sizes.json').write_text(json.dumps(sizes,indent=2)+'\n')
print('CHECK PASSED: partial results only; universal R1, R2, R3 remain unproved.',flush=True)
