#!/usr/bin/env python3
"""Offline, fail-closed checks; generated evidence goes in .verification/."""
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
os.chdir(ROOT)
OUT = ROOT / '.verification'
OUT.mkdir(exist_ok=True)
ENV = dict(os.environ, XDG_CACHE_HOME=str(OUT / 'cache'))
BIN = Path(shutil.which('lean')).resolve().parent
THEOREMS = ['encoder_block_invalid', 'late_match', 'valid_block_content',
            'valid_content_length', 'empty_block_content', 'wrong_return', 'outside_block']


def run(args, label, reject=False, reason=None):
    p = subprocess.run([str(x) for x in args], env=ENV, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / (label + '.log')).write_text(p.stdout)
    if reject:
        assert p.returncode != 0, f'{label}: accepted a false control'
        assert reason in p.stdout, f'{label}: failed for the wrong reason:\n{p.stdout}'
        print(f'PASS {label}: false control rejected', flush=True)
    else:
        assert p.returncode == 0, f'{label}:\n{p.stdout}'
        print(f'PASS {label}', flush=True)
    return p.stdout


def export(module, names, label):
    text = run(['lake', 'env', BIN / 'leanexport', module, '--', *names], label)
    path = OUT / (label + '.ndjson')
    path.write_text(text)
    return path


def read_export(path):
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    names = {0: ''}
    decls = {}
    for row in rows:
        if 'in' in row:
            part = row.get('str', row.get('num'))
            names[row['in']] = (names[part['pre']] + ('.' if part['pre'] else '') +
                                str(part.get('str', part.get('i'))))
        for tag in ('thm', 'def', 'axiom'):
            if tag in row:
                decls[names[row[tag]['name']]] = row[tag]
        if 'axiom' in row:
            assert names[row['axiom']['name']] == 'propext', 'unapproved axiom'
        if 'def' in row:
            assert row['def']['safety'] == 'safe', 'unsafe proof dependency'
    return rows, names, decls


def kernels(path, label, reject=False):
    cfg = OUT / (label + '.json')
    cfg.write_text(json.dumps({
        'export_file_path': str(path), 'permitted_axioms': ['propext'],
        'unpermitted_axiom_hard_error': True, 'nat_extension': True,
        'string_extension': True, 'pp_declars': [], 'print_success_message': True}))
    run(['lake', 'env', BIN / 'leanchecker', '--from-export', path],
        label + '-lean', reject, 'declaration type mismatch' if reject else None)
    run([BIN / 'nanoda_bin', cfg], label + '-nanoda', reject,
        'src/tc.rs' if reject else None)


expected_hashes = {
    'lz4-block-codec.wasm': '4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf',
    'lz4-block-codec.wat': '737b63992149810690086420d4802d86db058359c998768a9737962c974250e3',
    'lz4_Block_format.md': 'dce3c34a8738c44ed1dffb48c73e30297fca98ba7881408dc228865912c9a42e'}
for name, expected in expected_hashes.items():
    assert hashlib.sha256(Path(name).read_bytes()).hexdigest() == expected, name
assert Path('lz4-block-codec.wasm').stat().st_size == 1226
print('PASS artifact/spec/source SHA-256 and artifact size', flush=True)
run(['wasm-tools', 'validate', 'lz4-block-codec.wasm'], 'wasm-validation')
run(['wasm-tools', 'print', 'lz4-block-codec.wasm'], 'artifact-disassembly')
run(['lake', 'env', 'lean', '--version'], 'lean-version')
assert 'version 4.35.0' in (OUT / 'lean-version.log').read_text()

# Force recompilation, rather than relying on previously cached project proofs.
lib = ROOT / '.lake/build/lib/lean'
(lib / 'Proofs').mkdir(parents=True, exist_ok=True)
for source in ['Proofs/Format', 'Proofs', 'Controls']:
    run(['lake', 'env', 'lean', '-o', lib / (source + '.olean'), source + '.lean'],
        'compile-' + source.replace('/', '-'))
proofs = export('Proofs', ['Verification.' + n for n in THEOREMS], 'proofs')
_, _, declarations = read_export(proofs)
assert all('Verification.' + n in declarations for n in THEOREMS)
kernels(proofs, 'proofs')

# These valid proofs pass first, then their statements are changed to False
# and 0 = 1 while preserving the original proof terms.
controls = export('Controls', ['Controls.' + n for n in
                  ['truth', 'falseType', 'equal', 'unequal']], 'controls')
rows, names, declarations = read_export(controls)
kernels(controls, 'controls')
for label, theorem, bad_type in [('false', 'truth', 'falseType'),
                                ('zero-equals-one', 'equal', 'unequal')]:
    changed = copy.deepcopy(rows)
    index = next(i for i, row in enumerate(changed) if 'thm' in row and
                 names[row['thm']['name']] == 'Controls.' + theorem)
    row = changed.pop(index)
    row['thm']['type'] = declarations['Controls.' + bad_type]['value']
    changed.append(row)  # Replacement type must precede its use in NDJSON.
    path = OUT / (label + '.ndjson')
    path.write_text(''.join(json.dumps(row) + '\n' for row in changed))
    kernels(path, label, reject=True)

cases = run(['lake', 'env', 'lean', '--run', 'EmitCases.lean'], 'emit-cases')
json.loads(cases)
(OUT / 'cases.json').write_text(cases)
run(['node', 'runtime-check.mjs'], 'v8-runtime')
print((OUT / 'v8-runtime.log').read_text(), end='', flush=True)
run(['wasmtime', 'wast', OUT / 'runtime.wast'], 'wasmtime-runtime')
run(['wasmtime', 'wast', OUT / 'false-runtime.wast'], 'wasmtime-false-runtime',
    reject=True, reason='expected')

files = ['Proofs/Format.lean', 'Proofs.lean', 'EmitCases.lean', 'Controls.lean',
         'runtime-check.mjs', 'verify.py', 'check.sh', 'lakefile.toml', 'lean-toolchain',
         'lake-manifest.json']
sizes = '\n'.join(f'{name}: {len(Path(name).read_bytes().splitlines())} lines, '
                  f'{Path(name).stat().st_size} bytes' for name in files)
(OUT / 'sizes.txt').write_text(sizes + '\n')
print(sizes, flush=True)
print('ALL CHECKS PASSED: R1, R2, R3 are refuted on the shipped artifact.', flush=True)
