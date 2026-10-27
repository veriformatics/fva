#!/usr/bin/env python3
"""Offline replay, artifact binding, independent kernels, and negative controls."""
import ast
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent.parent
os.chdir(ROOT)
os.environ['LEAN_NUM_THREADS'] = '2'
OUT = ROOT / 'verification' / 'out'
OUT.mkdir(exist_ok=True)
BIN = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip()) / 'bin'
ROOTS = ['Artifact.edge_bytes', 'Artifact.rna_bytes', 'Artifact.first_gap',
         'Artifact.R3_false', 'Artifact.different_truncated_10',
         'Artifact.different_rounded_10', 'TMM.matrix_shape', 'TMM.quartiles',
         'TMM.reference_correct', 'TMM.cutoff_irrelevant', 'TMM.first_factor_upper',
         'TMM.R1_exact_counterexample', 'TMM.R2_exact_counterexample']

def run(args, name, *, reject=None, env=None):
    print(f'Checking {name} ...', flush=True)
    result = subprocess.run(args, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, env=env)
    (OUT / (name + '.log')).write_text(result.stdout)
    if reject is None:
        if result.returncode:
            raise RuntimeError(f'{name} failed ({result.returncode}):\n{result.stdout}')
    else:
        if result.returncode == 0 or reject not in result.stdout:
            raise RuntimeError(f'{name} did not reject for the expected reason:\n{result.stdout}')
    print(f'  {"REJECTED as expected" if reject else "PASS"}', flush=True)
    return result.stdout

def export(module, names, target, env=None):
    with target.open('w') as out:
        subprocess.run(['lake', 'env', str(BIN / 'leanexport'), module, '--', *names],
                       stdout=out, check=True, env=env)

def nanoda(target, name, reject=None):
    config = OUT / (name + '.json')
    config.write_text(json.dumps({'export_file_path': str(target),
        'permitted_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'unpermitted_axiom_hard_error': True, 'nat_extension': True,
        'string_extension': True, 'print_success_message': True}))
    run([str(BIN / 'nanoda_bin'), str(config)], name, reject=reject)

# These checks are deliberately separate from mathematical proofs: they bind the
# constants in the theorem statements to the actual, unmodified input bytes.
manifest = json.loads(Path('verification/inputs.json').read_text())
for name, digest in manifest.items():
    if hashlib.sha256(Path(name).read_bytes()).hexdigest() != digest:
        raise RuntimeError('Input hash mismatch: ' + name)
source = Path('Proofs/Artifact.lean').read_text()
for const, path in [('edgeBytes','edger-factors.txt'), ('rnaBytes','rnanorm-factors.txt')]:
    literal = re.search(r'def '+const+r' : List \(List Nat\) := (\[[^\n]*\])', source)[1]
    data = b'\n'.join(bytes(line) for line in ast.literal_eval(literal)) + b'\n'
    if data != Path(path).read_bytes():
        raise RuntimeError('Byte binding mismatch: ' + path)
literal = re.search(r'def counts : Matrix := (\[[^\n]*\])', Path('Proofs/DataBase.lean').read_text())[1]
data = ''.join('\t'.join(map(str, row))+'\n' for row in ast.literal_eval(literal)).encode('ascii')
if data != Path('counts.tsv').read_bytes():
    raise RuntimeError('Byte binding mismatch: counts.tsv')
print('PASS: input hashes and exact byte bindings', flush=True)

# Never rely on preexisting project object files. Package caches remain intact.
shutil.rmtree('.lake/build', ignore_errors=True)
run(['lake', '--no-cache', 'build'], 'build')
run(['lake', 'env', 'lean', 'verification/Audit.lean'], 'axioms')
export('Proofs', ROOTS, OUT / 'proofs.ndjson')
run(['python3','verification/footprint.py',str(OUT/'proofs.ndjson'),
     str(OUT/'footprint.json'),*ROOTS], 'footprint')
run([str(BIN / 'leanchecker'), '--from-export', str(OUT / 'proofs.ndjson')], 'lean-kernel')
nanoda(OUT / 'proofs.ndjson', 'nanoda-kernel')

# A well-formed false theorem: the elaborator's kernel check is deliberately
# bypassed ONLY for this isolated negative fixture, never for a proof above.
run(['lake','env','lean','-o',str(OUT/'Reject.olean'),'verification/Reject.lean'], 'make-forgery')
run(['lake','env','lean','-o',str(OUT/'Positive.olean'),'verification/Positive.lean'], 'make-control')
fixture_env = dict(os.environ)
fixture_env['LEAN_PATH'] = str(OUT) + os.pathsep + fixture_env.get('LEAN_PATH', '')
export('Positive', ['positive_control'], OUT / 'positive.ndjson', fixture_env)
export('Reject', ['KnownFalse'], OUT / 'false.ndjson', fixture_env)
export('Reject', ['KnownFalseArithmetic'], OUT / 'false-arithmetic.ndjson', fixture_env)
run([str(BIN/'leanchecker'),'--from-export',str(OUT/'positive.ndjson')], 'lean-positive')
nanoda(OUT/'positive.ndjson', 'nanoda-positive')
run([str(BIN/'leanchecker'),'--from-export',str(OUT/'false.ndjson')],
    'lean-negative', reject='declaration type mismatch')
nanoda(OUT/'false.ndjson', 'nanoda-negative', reject='self.def_eq')
run([str(BIN/'leanchecker'),'--from-export',str(OUT/'false-arithmetic.ndjson')],
    'lean-negative-arithmetic', reject='declaration type mismatch')
nanoda(OUT/'false-arithmetic.ndjson', 'nanoda-negative-arithmetic', reject='self.def_eq')

# This is execution evidence in the R runtime, separate from the exact-real theorem.
run(['Rscript','verification/replay.R'], 'edger-replay')
print('ALL CHECKS PASSED: mathematical counterexamples and R3 failure verified; both kernels reject the forgery.', flush=True)
