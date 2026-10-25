#!/usr/bin/env python3
"""Fresh compilation, binary binding, independent kernels, negative controls."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
from extract import extract, SHA256
from runtime import scripts

ROOT = Path(__file__).resolve().parents[1]
assert Path.cwd() == ROOT, 'run from the project directory'
OUT = ROOT / '.verification'
OUT.mkdir(exist_ok=True)
LIB = OUT / 'lib'
(LIB / 'Proofs').mkdir(parents=True, exist_ok=True)
ENV = dict(os.environ)
ENV['LEAN_PATH'] = str(LIB) + os.pathsep + ENV.get('LEAN_PATH', '')
ENV['XDG_CACHE_HOME'] = str(OUT / 'cache')
BIN = Path(shutil.which('lean')).resolve().parent
ROOTS = ['Verification.R1_counterexample', 'Verification.R2_counterexample', 'Verification.R3_counterexample']

def run(args, name, accept=(0,), contains=None):
    p = subprocess.run([str(x) for x in args], env=ENV, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
    (OUT / f'{name}.log').write_text(p.stdout)
    if p.returncode not in accept or (contains and contains not in p.stdout):
        raise RuntimeError(f'{name}: exit {p.returncode}\n{p.stdout}')
    print(f'PASS {name}', flush=True)
    return p.stdout

def export(module, roots, stem):
    data = run([BIN/'leanexport', module, '--', *roots], stem)
    path = OUT / f'{stem}.ndjson'
    path.write_text(data)
    return path

def kernels(path, stem, reject=False, axiom=False):
    config = {'export_file_path':str(path), 'permitted_axioms':['propext'],
              'unpermitted_axiom_hard_error':True, 'nat_extension':True,
              'string_extension':True, 'pp_declars':[], 'print_success_message':True}
    cfg = OUT / f'{stem}.json'
    cfg.write_text(json.dumps(config))
    run([BIN/'nanoda_bin', cfg], f'{stem}-nanoda',
        (1,) if axiom else ((101,) if reject else (0,)),
        'unpermitted axiom' if axiom else ('self.def_eq' if reject else 'no typechecker errors'))
    run([BIN/'con-ron', '--verified', '--jobs=2', path], f'{stem}-con-ron',
        (2,) if axiom else ((1,) if reject else (0,)),
        'declined: use of the sorryAx axiom' if axiom else ('rejected' if reject else 'accepted'))

assert (ROOT/'Proofs/Artifact.lean').read_text() == extract(), 'stale binary extraction'
run(['wasm-tools','validate','lz4-block-codec.wasm'], 'wasm-validation')
for module in ['Wasm','Artifact','LZ4','Counterexamples']:
    run([BIN/'lean','-o',LIB/'Proofs'/f'{module}.olean',f'Proofs/{module}.lean'], f'lean-{module}')
run([BIN/'lean','-o',LIB/'Proofs.olean','Proofs.lean'], 'lean-root')
proofs = export('Proofs', ROOTS, 'proofs')
# An explicit allowlist also protects checkers with implicit prelude axioms.
records = [json.loads(line) for line in proofs.read_text().splitlines()]
names = {0:''}
for r in records:
    if 'in' in r:
        n = r.get('str', r.get('num'))
        part = n['str'] if 'str' in n else str(n['i'])
        names[r['in']] = (names[n['pre']]+'.' if names[n['pre']] else '')+part
axioms = [names[r['axiom']['name']] for r in records if 'axiom' in r]
assert axioms == ['propext'], axioms
assert all(any('thm' in r and names[r['thm']['name']] == root for r in records) for root in ROOTS)
kernels(proofs, 'proofs')
# This bypasses elaborator unification and submits Eq.refl 0 : 0=1 to Lean's kernel.
run([BIN/'lean','verification/KernelNegative.lean'], 'false-proof-lean', (1,), '(kernel) declaration type mismatch')
# Check acceptance of the control before forging its exported type.
run([BIN/'lean','-o',LIB/'Controls.olean','verification/Controls.lean'], 'control-build')
control = export('Controls',['Verification.Controls.control'],'control')
kernels(control, 'control')
rs = [json.loads(line) for line in control.read_text().splitlines()]
exprs = {r['ie']:r for r in rs if 'ie' in r}
th = rs[-1]['thm']
top = exprs[th['type']]['app']
n = max(exprs)+1
rs[-1:-1] = [{'ie':n,'natVal':'1'}, {'ie':n+1,'app':{'fn':top['fn'],'arg':n}}]
th['type'] = n+1  # Eq Nat 0 1, with the unchanged proof Eq.refl Nat 0.
forged = OUT/'false-proof.ndjson'
forged.write_text('\n'.join(json.dumps(r) for r in rs)+'\n')
kernels(forged, 'false-proof', reject=True)
# Also reject a false theorem admitted through sorryAx, rather than type mismatch.
sorry = OUT/'SorryControl.lean'
sorry.write_text('theorem sorryControl : False := by sorry\n')
run([BIN/'lean',f'--root={OUT}','-o',LIB/'SorryControl.olean',sorry], 'sorry-build')
sorry_export = export('SorryControl',['sorryControl'],'sorry-control')
kernels(sorry_export, 'sorry-control', reject=True, axiom=True)
scripts(OUT)
for req in ['R1','R2','R3']:
    run(['wasmtime','wast',OUT/f'{req}.wast'], f'runtime-{req}')
run(['wasmtime','wast',OUT/'wrong-runtime.wast'], 'false-runtime-assertion', (1,), "didn't match")
files = ['Proofs/Wasm.lean','Proofs/LZ4.lean','Proofs/Counterexamples.lean','Proofs/Artifact.lean',
         'Proofs.lean','verification/extract.py','verification/runtime.py','verification/check.py',
         'verification/Controls.lean','verification/KernelNegative.lean','check.sh']
sizes = {f:{'lines':len(Path(f).read_bytes().splitlines()),'bytes':Path(f).stat().st_size} for f in files}
counts = {k:sum(k in r for r in records) for k in ['def','thm','axiom','inductive','opaque']}
summary = {'artifact':{'bytes':1226,'sha256':SHA256},'axioms':axioms,
           'source_sizes':sizes,'export_records':len(records),'declarations':counts,
           'export_bytes':proofs.stat().st_size,'export_sha256':hashlib.sha256(proofs.read_bytes()).hexdigest()}
(OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
print('ALL CHECKS PASSED: R1, R2, R3 refuted; three kernels checked; forged proofs and unsafe axioms blocked.')
