#!/usr/bin/env python3
"""Offline, fail-closed artifact binding, proof replay, and adversarial controls."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

if not __debug__:
    sys.exit('Run Python without optimization: assertions are required')

ROOT = Path(__file__).resolve().parent.parent
if Path.cwd().resolve() != ROOT:
    sys.exit('Run from the project directory: python3 verification/check.py')
OUT = ROOT / '.verification'
OUT.mkdir(exist_ok=True)
TARGETS = ['Verification.' + n for n in (
    'R1_failure', 'R2_failure', 'R3_failure', 'first_TMM_lt', 'first_difference',
    'shape', 'reference', 'cutoff_irrelevant', 'quantiles_above_fallback', 'tied_boundary')]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def run(args, label, expected=0, dest=None):
    log = dest or OUT / (label + '.log')
    with open(log, 'wb') as stream:
        result = subprocess.run(args, stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode != expected:
        sys.exit(f'FAIL {label}: exit {result.returncode}, expected {expected}; see {log}')
    print(f'PASS {label}', flush=True)
    return log

def audit(path, targets):
    names = {0: ''}
    declared = set()
    axioms = set()
    counts = {}
    for line in path.open():
        row = json.loads(line)
        if 'in' in row:
            v = row.get('str', row.get('num'))
            names[row['in']] = (names[v['pre']] + '.' + str(v.get('str', v.get('i')))).lstrip('.')
        for kind in ('def', 'thm', 'opaque', 'axiom', 'inductive', 'quot'):
            if kind in row:
                counts[kind] = counts.get(kind, 0) + 1
                if kind in ('def', 'thm', 'opaque', 'axiom'):
                    declared.add(names[row[kind]['name']])
                if kind == 'axiom':
                    axioms.add(names[row[kind]['name']])
    assert set(targets) <= declared, ('missing targets', set(targets) - declared)
    assert axioms <= ALLOWED, ('unapproved axioms', axioms - ALLOWED)
    assert counts.get('thm', 0) >= len(targets)
    return dict(declarations=counts, axioms=sorted(axioms), bytes=path.stat().st_size,
                sha256=hashlib.sha256(path.read_bytes()).hexdigest())

manifest = json.loads(Path('verification/artifacts.json').read_text())
for path, digest in manifest.items():
    assert hashlib.sha256(Path(path).read_bytes()).hexdigest() == digest, ('artifact changed', path)
print(f'PASS exact artifact bytes ({len(manifest)} files)', flush=True)
# The small input reader is the only translation from files into theorem inputs.
run([sys.executable, 'verification/input.py'], 'input-binding')
# Never accept stale local oleans; installed Mathlib is left intact.
shutil.rmtree('.lake/build', ignore_errors=True)
run(['lake', 'build'], 'lean-build')
proof = run(['lake', 'env', 'leanexport', 'Proofs', '--', *TARGETS],
            'export', dest=OUT / 'proof.ndjson')
report = audit(proof, TARGETS)
print('PASS axiom and target audit', flush=True)
run(['lake', 'env', 'leanchecker', '--from-export', str(proof)], 'cpp-kernel')
run(['lake', 'env', 'con-ron', '--verified', '--jobs=2', str(proof)], 'rust-kernel')

run(['lake', 'env', 'lean', '-o', '.lake/build/lib/lean/VerificationControls.olean',
     'verification/Controls.lean'], 'compile-controls')
good = run(['lake', 'env', 'leanexport', 'VerificationControls', '--',
            'verificationArithmeticControl', 'verificationFalseControl'],
           'export-controls', dest=OUT / 'controls.ndjson')
audit(good, ['verificationArithmeticControl', 'verificationFalseControl'])
records = [json.loads(line) for line in good.open()]
names = {0: ''}
for row in records:
    if 'in' in row:
        v = row.get('str', row.get('num'))
        names[row['in']] = (names[v['pre']] + '.' + str(v.get('str', v.get('i')))).lstrip('.')
false_name = next(i for i, name in names.items() if name == 'False')
false_expr = next(r['ie'] for r in records if r.get('const', {}).get('name') == false_name)
for checker, prefix in [('cpp', ['lake', 'env', 'leanchecker', '--from-export']),
                        ('rust', ['lake', 'env', 'con-ron', '--verified', '--jobs=2'])]:
    run(prefix + [str(good)], checker + '-valid-control')
    for attack in ('arithmetic', 'false'):
        bad = json.loads(json.dumps(records))
        if attack == 'arithmetic':
            changed = [r for r in bad if r.get('natVal') == '42']
            assert len(changed) == 1
            changed[0]['natVal'] = '43'
        else:
            changed = [r['thm'] for r in bad if 'thm' in r and
                       names[r['thm']['name']] == 'verificationFalseControl']
            assert len(changed) == 1
            changed[0]['type'] = false_expr
        bad_path = OUT / (attack + '.ndjson')
        bad_path.write_text(''.join(json.dumps(r) + '\n' for r in bad))
        log = run(prefix + [str(bad_path)], checker + '-reject-' + attack, expected=1)
        assert 'type mismatch' in log.read_text(), ('not a type-checking rejection', log)

# Source replays are diagnostic evidence, separate from the kernel proofs.
run(['Rscript', '--vanilla', 'verification/reproduce.R'], 'edgeR-source-replay')
run([sys.executable, 'verification/reproduce.py'], 'RNAnorm-method-replay')
report['custom_files'] = {str(p): dict(bytes=p.stat().st_size,
    lines=len(p.read_text().splitlines())) for p in sorted(Path('Proofs').glob('*.lean'))}
(OUT / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
print('VERIFICATION SUCCESS: all three requirements refuted at tolerance 1e-10;', flush=True)
print('C++ and Rust kernels accepted the proofs and rejected both false-proof controls.')
