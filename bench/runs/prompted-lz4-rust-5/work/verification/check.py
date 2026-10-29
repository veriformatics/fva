#!/usr/bin/env python3
"""One offline check, from raw module bytes to independent kernel replay."""
import hashlib
import json
import os
import subprocess
from pathlib import Path
from checkers import KERNELS, names_and_audit, kernel, forge_controls
from runtime import check_runtime

ROOT = Path(__file__).resolve().parent.parent
os.chdir(ROOT)
OUT = ROOT/'verification/out'
OUT.mkdir(exist_ok=True)

def call(args, log=None, env=None):
    print('+ '+' '.join(map(str,args)),flush=True)
    if log:
        with log.open('w') as f:
            subprocess.run(args,check=True,stdout=f,stderr=subprocess.STDOUT,env=env)
    else:
        subprocess.run(args,check=True,env=env)

for binary in KERNELS.values():
    assert Path(binary).is_file(), f'required independent kernel missing: {binary}'
call(['python3','verification/extract.py','--check'])
call(['python3','verification/samples.py','--check'])
call(['python3','verification/traces.py','--check'])
call(['wasm-tools','validate','lz4-flex.wasm'])
# Compile all local modules afresh. No local .olean is accepted from a prior run.
lib = ROOT/'.lake/build/lib/lean'
(lib/'Proofs').mkdir(parents=True,exist_ok=True)
for name in ['Wasm','Artifact','Format','Samples','Claims','Traces','Cases']:
    call(['lake','env','lean','-DwarningAsError=true','-o',str(lib/'Proofs'/(name+'.olean')),
          f'Proofs/{name}.lean'],OUT/(name+'.build.log'))
call(['lake','env','lean','-DwarningAsError=true','-o',str(lib/'Proofs.olean'),'Proofs.lean'],
     OUT/'root.build.log')
roots = ['Verification.zero_input','Verification.buffers_admissible',
         'Verification.samples_format','Verification.samples_artifact']
proofs = OUT/'proofs.ndjson'
call(['lake','env','lean','--run','verification/export.lean','Proofs']+roots,proofs)
audit,_ = names_and_audit(proofs,set(roots))
print('export audit: '+json.dumps(audit),flush=True)
for kind in KERNELS:
    kernel(kind,proofs,OUT,True)
# Positive control and two well-formed, ill-typed proof terms for every kernel.
call(['lake','env','lean','-DwarningAsError=true','-o',str(lib/'Negative.olean'),
      '--root=verification','verification/Negative.lean'],OUT/'negative.build.log')
good = OUT/'control.ndjson'
call(['lake','env','lean','--run','verification/export.lean','Negative',
      'Negative.unequal','Negative.bottom','Negative.good'],good)
false_files = forge_controls(good,OUT)
for kind in KERNELS:
    kernel(kind,good,OUT,True)
    for path in false_files:
        kernel(kind,path,OUT,False)
p = subprocess.run(['lake','env','lean','verification/KernelNegative.lean'],
                   capture_output=True,text=True)
log = p.stdout+p.stderr
(OUT/'kernel-negative.log').write_text(log)
assert p.returncode != 0 and log.count('(kernel)') >= 2, log
assert 'ForgedUnequal' in log and 'ForgedFalse' in log, log
print('Lean kernel: rejected both false declarations',flush=True)
check_runtime(OUT)
# Reproducible review-size inventory; generated data and proof bodies separated.
review = ['Proofs/Wasm.lean','Proofs/Format.lean','Proofs/Claims.lean','Proofs/Cases.lean',
          'verification/extract.py','verification/export.lean','verification/samples.py',
          'verification/check.py','verification/checkers.py','verification/runtime.py',
          'verification/Negative.lean','verification/KernelNegative.lean','check.sh','Proofs.lean']
inventory = {}
for name in review + ['Proofs/Artifact.lean','Proofs/Samples.lean','verification/cases.json','Proofs/Traces.lean','verification/traces.py']:
    raw = (ROOT/name).read_bytes()
    inventory[name] = dict(lines=len(raw.splitlines()),bytes=len(raw),
                          sha256=hashlib.sha256(raw).hexdigest())
summary = dict(coverage='partial; universal R1, R2, R3 unresolved',roots=roots,
              export=audit,review_files=review,inventory=inventory,
              kernels={k:hashlib.sha256(Path(p).read_bytes()).hexdigest() for k,p in KERNELS.items()})
(OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print('PASS: artifact-bound partial proofs, independent replay, false-proof rejection, runtime checks',flush=True)
print('UNRESOLVED: R1, R2, R3 for arbitrary inputs; this is not a full verification.',flush=True)
