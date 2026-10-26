#!/usr/bin/env python3
"""One offline command for the counterexamples, certificates, and negative controls."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
os.chdir(root)
out = root/'.verification'
out.mkdir(exist_ok=True)
env = dict(os.environ, XDG_CACHE_HOME=str(out/'cache'))
leanbin = Path(subprocess.check_output(['lean','--print-prefix'],text=True).strip())/'bin'
for name in ['leanexport','leanchecker','lean4lean']:
    assert (leanbin/name).is_file(), f'Missing {leanbin/name}'
for name in ['lake','python3','node','Rscript','wasm-tools','wasmtime','sha256sum']:
    assert shutil.which(name), f'Missing {name}'

def run(label, cmd, *, save=None, reject=None):
    p = subprocess.run(list(map(str,cmd)),env=env,text=True,
        stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=180)
    log = p.stdout+p.stderr
    (out/(label+'.log')).write_text(log)
    if reject:
        assert p.returncode == 1 and all(s in log for s in reject), (
            f'{label}: wrong rejection (exit {p.returncode})\n'+log[-5000:])
        print('REJECTED known false claim:',label,flush=True)
    else:
        assert p.returncode == 0, f'{label} failed (exit {p.returncode})\n{log[-5000:]}'
        if save:
            save.write_text(p.stdout)
        elif log:
            print(log.strip(),flush=True)
        print('PASS:',label,flush=True)
    return log

run('artifact-hashes',['sha256sum','-c','verification/artifacts.sha256'])
run('wasm-validation',['wasm-tools','validate','edgeR.so'])
run('wast-generation',[sys.executable,'verification/wast.py',out])
run('wasmtime',['wasmtime','wast',out/'artifact.wast'])
run('v8',['node','verification/wasm.mjs'])
run('r-filter',['Rscript','--vanilla','verification/filter.R'])
# Compile every local proof from source on every run, regardless of Lake's cache.
olean = root/'.lake/build/lib/lean/Proofs/Arithmetic.olean'
olean.parent.mkdir(parents=True,exist_ok=True)
run('lean-source',['lake','env','lean','Proofs/Arithmetic.lean','-o',olean])
targets = ['Verification.r1_exact_and_overflow','Verification.r2_rounding_intervals',
           'Verification.r2_fractional_sample_threshold']
certificate = out/'proofs.export'
run('lean-export',['lake','env',leanbin/'leanexport','Proofs.Arithmetic','--',*targets],save=certificate)
run('export-audit',[sys.executable,'verification/audit.py',certificate])
run('lean-kernel',['lake','env',leanbin/'leanchecker','--from-export',certificate])
log = run('lean4lean',['lake','env',leanbin/'lean4lean','--import',certificate])
assert re.search(r'checked [1-9][0-9]* declarations',log), 'Empty independent replay'
for case in ['false-proposition','false-equality']:
    for checker,flag in [('leanchecker','--from-export'),('lean4lean','--import')]:
        run(f'{case}-{checker}', ['lake','env',leanbin/checker,flag,out/(case+'.export')],
            reject=['(kernel) declaration type mismatch','KnownFalseProof'])
run('false-axiom-audit',[sys.executable,'verification/audit.py',out/'false-axiom.export'],
    reject=['AssertionError','KnownFalseAxiom'])
run('false-wasm-result',['wasmtime','wast',out/'false-artifact.wast'],
    reject=['expected','actual'])
run('false-v8-result',['node','verification/wasm.mjs','negative'],
    reject=['AssertionError','555555'])
run('false-r-result',['Rscript','--vanilla','verification/filter.R','negative'],
    reject=['all(kept) is not TRUE'])
files = [Path('Proofs/Arithmetic.lean'),*sorted(Path('verification').glob('*.py')),
         Path('verification/wasm.mjs'),Path('verification/filter.R')]
for path in files:
    b = path.read_bytes()
    print(f'REVIEW SIZE: {path}: {len(b.splitlines())} lines, {len(b)} bytes')
print('ALL CHECKS PASSED: requirement counterexamples reproduced; '
      'certificates accepted by two kernels; negative controls rejected.',flush=True)
