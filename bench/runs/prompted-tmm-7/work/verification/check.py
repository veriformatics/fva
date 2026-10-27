"""One offline command: fresh build, byte binding, independent replay, negative controls."""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess as S
import sys
import tempfile
import time
from audit import audit

assert Path.cwd()==Path(__file__).resolve().parent.parent, 'run from the project directory'
BASE=Path('verification')
LEANBIN=Path(S.check_output(['lean','--print-prefix'],text=True).strip())/'bin'
ENV=dict(os.environ,RUST_MIN_STACK=str(64*1024*1024))

def run(args, name, success=None, reject=False):
    print(('Reject control: ' if reject else 'Check: ')+name,flush=True)
    started=time.monotonic()
    p=S.run(list(map(str,args)),stdout=S.PIPE,stderr=S.STDOUT,text=True,env=ENV)
    (BASE/(name+'.log')).write_text(p.stdout)
    if reject:
        assert p.returncode!=0, f'{name}: false proof unexpectedly accepted\n{p.stdout[-4000:]}'
    else:
        assert p.returncode==0, f'{name} failed\n{p.stdout[-8000:]}'
    if success: assert re.search(success,p.stdout), f'{name}: missing expected verdict\n{p.stdout[-8000:]}'
    print(f'PASS: {name} ({time.monotonic()-started:.1f}s)',flush=True)
    return p

for line in (BASE/'artifacts.sha256').read_text().splitlines():
    digest,path=line.split(maxsplit=1)
    assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==digest, 'changed shipped file: '+path
run([sys.executable,BASE/'embed.py','--check'],'artifact-byte-binding')
# Test the actual byte comparator in an isolated directory, leaving shipped files untouched.
with tempfile.TemporaryDirectory() as tmp:
    root=Path(tmp)
    (root/'Proofs').mkdir()
    for f in ['counts.tsv','edger-factors.txt','rnanorm-factors.txt','Proofs/Artifacts.lean']:
        shutil.copyfile(f,root/f)
    for f in ['counts.tsv','edger-factors.txt','rnanorm-factors.txt']:
        old=(root/f).read_bytes()
        (root/f).write_bytes(bytes([old[0]^1])+old[1:])
        p=S.run([sys.executable,str((BASE/'embed.py').resolve()),'--check'],cwd=root,capture_output=True)
        assert p.returncode!=0, 'byte comparator accepted changed '+f
        (root/f).write_bytes(old)
print('PASS: all three changed-artifact controls rejected',flush=True)
shutil.rmtree('.lake/build',ignore_errors=True)
run(['lake','build'],'fresh-lean-build',r'Build completed successfully')
roots=(BASE/'roots.txt').read_text().split()
print('Check: export complete proof dependencies',flush=True)
with (BASE/'proofs.ndjson').open('w') as out:
    S.run(['lake','env','lean','--run',str(BASE/'Export.lean'),*roots],stdout=out,check=True,env=ENV)
run([sys.executable,BASE/'review.py','--check'],'review-slice')
closure=audit(BASE/'proofs.ndjson')
(BASE/'closure.json').write_text(json.dumps(closure,indent=2)+'\n')
run(['lake','env','leanchecker','--from-export',BASE/'proofs.ndjson'],
    'lean-replay',r'Lean default kernel accepts the solution')
run([LEANBIN/'con-ron','--jobs=2',BASE/'proofs.ndjson'],
    'con-ron',r'con-ron: accepted [0-9]+ declarations \(--verified\)')
run(['lake','env','lean',BASE/'KnownFalse.lean'],'lean-false',r'Type mismatch',reject=True)
run([sys.executable,BASE/'negative.py'],'construct-false')
run(['lake','env','leanchecker','--from-export',BASE/'false.ndjson'],
    'lean-replay-false',r'rejects the solution.*|declaration type mismatch',reject=True)
run([LEANBIN/'con-ron','--jobs=2',BASE/'false.ndjson'],
    'con-ron-false',r'rejected: type mismatch',reject=True)
run(['Rscript',BASE/'reproduce.R'],'edgeR-reproduction',r'reproduces all artifact bytes')
print('ALL VERIFICATION CHECKS PASSED (the R3 requirement is refuted).',flush=True)
