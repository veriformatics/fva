#!/usr/bin/env python3
"""Rebuild, bind to bytes, audit axioms, and replay good and false proof exports."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent.parent
os.chdir(ROOT)
OUT = ROOT / '.verification'
OUT.mkdir(exist_ok=True)
BIN = Path(shutil.which('lean')).resolve().parent
KERNEL = BIN / 'leanchecker'
RUST = BIN / 'nanoda_bin'
EXPORT = BIN / 'leanexport'
for tool in [KERNEL, RUST, EXPORT]:
    assert tool.is_file(), f'Missing installed checker: {tool}'

def run(args, *, stdout=None):
    print('+', ' '.join(map(str,args)), flush=True)
    subprocess.run(list(map(str,args)), check=True, stdout=stdout)

# Pin every supplied input, producer, source and requirement document.
for line in Path('verification/artifacts.sha256').read_text().splitlines():
    digest, path = line.split('  ', 1)
    assert hashlib.sha256(Path(path).read_bytes()).hexdigest() == digest, path
print('All supplied artifact/source/document SHA-256 hashes match', flush=True)
embedded = Path('Proofs/Artifact.lean').read_bytes()
run(['python3','verification/embed.py'])
assert Path('Proofs/Artifact.lean').read_bytes() == embedded, 'Stale or edited embedding'
# Force the local proofs to rebuild, without rebuilding the supplied Mathlib installation.
shutil.rmtree('.lake/build/lib/lean/Proofs', ignore_errors=True)
Path('.lake/build/lib/lean/Proofs.olean').unlink(missing_ok=True)
run(['lake','build'])

statements = ['R1_statement','R2_statement','R2_literal_statement','R3_statement','R3_witness_statement']
targets = ['matrix_shape','library_sizes','quartile_brackets','reference_is_four',
           'eligible_count','retained_count','cutoff_safe','R1_fails','R2_fails',
           'R2_literal_bullet_fails','R3_counterexample','R3_fails'] + statements
export = OUT / 'proofs.ndjson'
with export.open('w') as f:
    run(['lake','env',EXPORT,'Proofs','--',*['Verification.'+s for s in targets]],stdout=f)

# An allowlist is essential: neither sorry nor an extra axiom is a proof.
def audit(path, expected):
    names={0:''}; found=set(); axioms=[]; counts={'thm':0,'def':0,'inductive':0}
    for line in path.open():
        row=json.loads(line)
        if 'in' in row:
            if 'str' in row:
                d=row['str']; names[row['in']]='.'.join(filter(None,[names[d['pre']],d['str']]))
            elif 'num' in row:
                d=row['num']; names[row['in']]=names[d['pre']]+'.'+str(d['i'])
        for key in counts:
            counts[key] += key in row
        if 'axiom' in row:
            axioms.append(names[row['axiom']['name']])
        for key in ['thm','def']:
            if key in row:
                found.add(names[row[key]['name']])
    assert set(axioms) <= {'propext','Classical.choice','Quot.sound'}, axioms
    assert set(expected) <= found, set(expected)-found
    print('Export audit:',counts,'axioms:',axioms, flush=True)
    return dict(counts, axioms=axioms, bytes=path.stat().st_size)

def rust(path, *, capture=False):
    cfg=OUT / 'nanoda.json'
    cfg.write_text(json.dumps({'export_file_path':str(path),
        'permitted_axioms':['propext','Classical.choice','Quot.sound'],
        'unpermitted_axiom_hard_error':True,'nat_extension':True,
        'string_extension':True,'print_success_message':True}))
    return subprocess.run([str(RUST),str(cfg)], capture_output=capture, text=True)

proof_metrics=audit(export,['Verification.'+s for s in targets])
statement_export=OUT/'statements.ndjson'
with statement_export.open('w') as f:
    run(['lake','env',EXPORT,'Proofs','--',*['Verification.'+s for s in statements]],stdout=f)
statement_metrics=audit(statement_export,['Verification.'+s for s in statements])
(OUT/'metrics.json').write_text(json.dumps({'proof_closure':proof_metrics,'statement_closure':statement_metrics},indent=2))
run([KERNEL,'--from-export',export])
assert rust(export).returncode == 0, 'Independent Rust kernel rejected the proofs'

# First accept well-formed fixtures, then alter only their claimed theorem types.
run(['lake','env','lean','-o',OUT/'Fixture.olean','verification/Fixture.lean'])
env=dict(os.environ,LEAN_PATH=str(OUT))
fixture=OUT/'fixture.ndjson'
with fixture.open('w') as f:
    subprocess.run([str(EXPORT),'Fixture','--','fixture_true','fixture_eq',
                    'fixture_false','fixture_neq'],env=env,stdout=f,check=True)
run([KERNEL,'--from-export',fixture])
assert rust(fixture).returncode == 0
run(['python3','verification/negative.py',str(fixture),str(OUT)])
for name in ['false','zero_one']:
    path=OUT/f'bad_{name}.ndjson'
    cpp=subprocess.run([str(KERNEL),'--from-export',str(path)],capture_output=True,text=True)
    assert cpp.returncode != 0 and 'declaration type mismatch' in cpp.stdout, cpp
    rs=rust(path,capture=True)
    assert rs.returncode != 0 and 'self.def_eq' in rs.stderr, rs
    (OUT/f'bad_{name}.log').write_text(cpp.stdout+cpp.stderr+rs.stdout+rs.stderr)
    print(f'Both kernels REJECTED the well-formed false proof: {name}', flush=True)
run(['Rscript','verification/runtime.R'])
print('SUCCESS: artifact bytes, all theorems, both independent kernels, and negative controls checked.',flush=True)
