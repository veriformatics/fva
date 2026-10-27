#!/usr/bin/env python3
"""Offline, fail-closed verification. Run from the project root."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
from negative import records, declarations, make_negatives

ROOT = Path(__file__).resolve().parent.parent
os.chdir(ROOT)
OUT = Path('.verification')
OUT.mkdir(exist_ok=True)
BIN = Path('/opt/lean/bin')
ROOTS = ['Verification.R1', 'Verification.R2', 'Verification.R2_literal',
         'Verification.R3', 'Verification.R3_gap', 'Verification.reference_is_four',
         'Verification.dimensions', 'Verification.libraries']
AXIOMS = ['propext', 'Classical.choice', 'Quot.sound']

def run(cmd, *, out=None, env=None):
    print('+', ' '.join(map(str, cmd)), flush=True)
    if out:
        with open(out, 'w') as f:
            subprocess.run(cmd, stdout=f, check=True, env=env)
    else:
        subprocess.run(cmd, check=True, env=env)

def check_export(path, roots):
    rs = records(path)
    assert rs and 'meta' in rs[0], f'Empty or invalid export: {path}'
    ds = declarations(rs)
    for name in roots:
        assert name in ds and ds[name][0] == 'thm', f'Missing theorem: {name}'
    # The independent checkers enforce the axiom policy too.
    for name, (kind, _) in ds.items():
        if kind == 'axiom':
            assert name in AXIOMS, f'Unapproved axiom: {name}'
    print(f'Export contains {len(ds)} named definitions/theorems/axioms and every requested root', flush=True)

def replay(name, *, negative=False):
    path = OUT / (name + '.ndjson')
    for checker in ('con-ron', 'con-leche', 'nanoda_bin'):
        if checker == 'nanoda_bin':
            config = dict(export_file_path=str(path), permitted_axioms=AXIOMS,
                          unpermitted_axiom_hard_error=False, nat_extension=True,
                          string_extension=True, pp_declars=[], print_success_message=True)
            cfg = OUT / (name + '.json')
            cfg.write_text(json.dumps(config))
            cmd = [str(BIN / checker), str(cfg)]
        else:
            cmd = [str(BIN / checker), '--verified', '--jobs=2', str(path)]
        print('+', ' '.join(cmd), flush=True)
        proc = subprocess.run(cmd, capture_output=True, text=True)
        log = proc.stdout + proc.stderr
        (OUT / (name + '.' + checker + '.log')).write_text(log)
        if negative:
            # Reject a type error, not a parse error, unsupported feature, or missing file.
            expected_code = 101 if checker == 'nanoda_bin' else 1
            marker = 'src/tc.rs' if checker == 'nanoda_bin' else 'type mismatch in theorem'
            assert proc.returncode == expected_code and marker in log, log
            print(f'{checker}: rejected known false proof {name} (type error)', flush=True)
        else:
            assert proc.returncode == 0, log
            if checker == 'nanoda_bin':
                assert 'no typechecker errors' in log, log
            else:
                assert 'accepted ' in log and '(--verified)' in log, log
            print(log.strip(), flush=True)

# Bind every original requirement, documentation, source, input and artifact byte.
manifest = json.loads(Path('verification/original-sha256.json').read_text())
for path, expected in manifest.items():
    assert hashlib.sha256(Path(path).read_bytes()).hexdigest() == expected, f'Changed shipped file: {path}'
print('Original-file SHA-256 checks passed', flush=True)
run([sys.executable, 'verification/embed.py'])
# Only this project's outputs are deleted. Prebuilt Mathlib remains untouched.
shutil.rmtree('.lake/build', ignore_errors=True)
run(['lake', 'build', 'Proofs'])
run(['lake', 'env', 'lean', '--run', 'verification/Export.lean', 'Proofs'] + ROOTS,
    out=OUT / 'proofs.ndjson')
check_export(OUT / 'proofs.ndjson', ROOTS)
replay('proofs')

run(['lake', 'env', 'lean', '-o', str(OUT / 'Controls.olean'), 'verification/Controls.lean'])
env = os.environ.copy()
env['LEAN_PATH'] = str(OUT)
controls = ['NegativeControls.control', 'NegativeControls.falseEquality', 'NegativeControls.falseArithmetic']
run(['lake', 'env', 'lean', '--run', 'verification/Export.lean', 'Controls'] + controls,
    out=OUT / 'controls.ndjson', env=env)
check_export(OUT / 'controls.ndjson', controls[:1])
replay('controls')
make_negatives()
for name, prop in [('falseEquality', '(0 : Nat) = 1'),
                   ('falseArithmetic', '(2 : Nat) + 2 = 5')]:
    bad = OUT / (name + '.lean')
    bad.write_text(f'theorem forged : {prop} := by rfl\n')
    proc = subprocess.run(['lake', 'env', 'lean', str(bad)], capture_output=True, text=True)
    log = proc.stdout + proc.stderr
    (OUT / (name + '.lean.log')).write_text(log)
    assert proc.returncode != 0 and 'rfl' in log and 'failed' in log, log
    print('Lean kernel: rejected', prop, flush=True)
    replay(name, negative=True)
run(['Rscript', '--vanilla', 'verification/replay.R'])
# Repeat original byte identity after checking.
for path, expected in manifest.items():
    assert hashlib.sha256(Path(path).read_bytes()).hexdigest() == expected
print('PASS: artifact-bound theorems replayed; all false-proof controls rejected.', flush=True)
