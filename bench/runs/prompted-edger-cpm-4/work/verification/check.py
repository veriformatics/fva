#!/usr/bin/env python3
"""Offline counterexample reproduction, proof replay, and rejection controls."""
import csv
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import struct
import subprocess
from fractions import Fraction

ROOT = Path(__file__).resolve().parent.parent
os.chdir(ROOT)
OUT = ROOT / '.verification'
if OUT.exists():
    shutil.rmtree(OUT)
OUT.mkdir()


def run(args, *, expect=0, logfile=None, env=None, cwd=ROOT):
    p = subprocess.run(list(map(str, args)), cwd=cwd, env=env,
                       text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if logfile:
        (OUT / logfile).write_text(p.stdout)
    if (expect == 0 and p.returncode != 0) or (expect != 0 and p.returncode == 0):
        raise RuntimeError(f'Unexpected status {p.returncode}: {args}\n{p.stdout}')
    return p.stdout


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def bits(x):
    return struct.unpack('<Q', struct.pack('<d', x))[0]


def double(x):
    return struct.unpack('<d', struct.pack('<Q', x))[0]


# Pin all supplied requirements, documentation, code, and the shipped binary.
for line in (ROOT / 'verification/inputs.sha256').read_text().splitlines():
    expected, name = line.split('  ', 1)
    require(hashlib.sha256(Path(name).read_bytes()).hexdigest() == expected,
            f'Input hash mismatch: {name}')
require(Path('edgeR.so').stat().st_size == 96558, 'Unexpected artifact size')
print('PASS: supplied artifact, sources, requirements and documentation hashes', flush=True)

# Decode for constructing imports only; the artifact itself is never rewritten.
run(['wasm-tools', 'validate', 'edgeR.so'])
run(['wasm-tools', 'print', 'edgeR.so', '-o', OUT / 'edgeR.wat'])
wat = (OUT / 'edgeR.wat').read_text()
imports = {'env': [], 'GOT.mem': [], 'GOT.func': []}
for line in wat.splitlines():
    match = re.fullmatch(r'  \(import "([^"]+)" "([^"]+)" (.*)\)', line)
    if not match:
        continue
    namespace, name, desc = match.groups()
    require(namespace in imports, f'Unexpected import namespace {namespace}')
    export = f'(export "{name}")'
    if desc.startswith('(func '):
        signature = ' '.join(re.findall(r'\((?:param|result) [^)]+\)', desc))
        body = 'unreachable'  # Every unused foreign call traps, including malloc.
        if name == 'R_chk_calloc':
            body = '''(local $p i32) (local $n i32)
              (if (i64.gt_u (i64.mul (i64.extend_i32_u (local.get 0))
                       (i64.extend_i32_u (local.get 1))) (i64.const 65536))
                (then unreachable))
              (local.set $n (i32.mul (local.get 0) (local.get 1)))
              (local.set $p (global.get $heap))
              (global.set $heap (i32.and
                (i32.add (i32.add (local.get $p) (local.get $n)) (i32.const 7))
                (i32.const -8)))
              (if (i32.gt_u (global.get $heap) (i32.const 1048576)) (then unreachable))
              (memory.fill (local.get $p) (i32.const 0) (local.get $n))
              (local.get $p)'''
        elif name == 'R_chk_free':
            body = '''(if (i32.or (i32.lt_u (local.get 0) (i32.const 262144))
                         (i32.ge_u (local.get 0) (global.get $heap))) (then unreachable))'''
        imports[namespace].append(f'(func {export} {signature} {body})')
    elif desc.startswith('(global '):
        ty = '(mut i32)' if '(mut i32)' in desc else 'i32'
        initial = {'__stack_pointer': 131072, '__memory_base': 4096}.get(name, 0)
        imports[namespace].append(f'(global {export} {ty} (i32.const {initial}))')
    elif desc.startswith('(memory '):
        imports[namespace].append(f'(memory {export} 16)')
    elif desc.startswith('(table '):
        imports[namespace].append(f'(table {export} 9 funcref)')
    else:
        raise RuntimeError(f'Unsupported import: {line}')
require(sum(map(len, imports.values())) == 151, 'Unexpected import count')
for namespace, decls in imports.items():
    extra = '(global $heap (mut i32) (i32.const 262144))' if namespace == 'env' else ''
    path = OUT / f'{namespace}.wat'
    path.write_text('(module\n' + extra + '\n' + '\n'.join(decls) + '\n)\n')
    run(['wasm-tools', 'parse', path, '-o', OUT / f'{namespace}.wasm'])
run(['wasm-tools', 'parse', 'verification/probe.wat', '-o', OUT / 'probe.wasm'])

cases = [
    {'name': 'overflow', 'count': str(0x7fe0000000000000), 'library': str(0x7fe0000000000000)},
    {'name': 'ten', 'count': str(bits(10.0)), 'library': str(bits(1e6))},
    {'name': 'twenty', 'count': str(bits(20.0)), 'library': str(bits(1e6))},
    {'name': 'zero', 'count': str(bits(0.0)), 'library': str(bits(1e6))},
]
(OUT / 'cases.json').write_text(json.dumps(cases, indent=2) + '\n')
node = json.loads(run(['node', 'verification/run.mjs', OUT], logfile='node.log'))
observed = []
for case in cases:
    args = ['wasmtime', 'run', '-C', 'cache=n']
    for namespace in imports:
        args += ['--preload', f'{namespace}={OUT / (namespace + ".wasm")}']
    args += ['--preload', 'edgeR=edgeR.so', '--invoke', 'cpm_bits',
             OUT / 'probe.wasm', case['count'], case['library']]
    output = run(args, logfile=f'wasmtime-{case["name"]}.log')
    numeric_lines = [s for s in output.splitlines() if re.fullmatch(r'-?\d+', s)]
    require(len(numeric_lines) == 1, 'Expected exactly one result from Wasmtime')
    observed.append({**case, 'output': str(int(numeric_lines[0]) % (2**64))})
require(observed == node, 'Wasmtime and Node disagree')
require([int(c['output']) for c in observed] ==
        [0x7ff0000000000000, bits(10.0), bits(20.0), bits(0.0)], 'Unexpected CPM outputs')
c = double(int(observed[0]['count']))
library = double(int(observed[0]['library']))
exact = Fraction(c) / Fraction(library) * 1000000
require(c == 2**1023 and library == c and library > 0, 'Invalid R1 input')
require(exact == 1000000 and Fraction(float(exact)) == exact, 'Target is not exact')
require(math.isinf(double(int(observed[0]['output']))), 'Overflow was not observed')
(OUT / 'observations.json').write_text(json.dumps(observed, indent=2) + '\n')
print('PASS: Wasmtime and Node execute original edgeR.so with identical outputs', flush=True)
print('R1: c=L=2^1023; exact CPM=1000000; observed bits=0x7ff0000000000000 (+infinity)', flush=True)

with (OUT / 'cpm.tsv').open('w') as f:
    f.write('count\tlibrary\tcpm\n')
    for case in observed[1:3]:
        f.write(f'{int(double(int(case["count"])))}\t{int(double(int(case["library"])))}'
                f'\t{double(int(case["output"]))}\n')
r_output = run(['Rscript', '--vanilla', 'verification/filter.R', OUT / 'cpm.tsv', OUT / 'filter.tsv'],
               logfile='R.log')
print(r_output, end='', flush=True)
with (OUT / 'filter.tsv').open() as f:
    rows = list(csv.DictReader(f, delimiter='\t'))
row = {k: int(v) for k, v in rows[0].items()}
require(row == {'count': 10, 'qualified': 1, 'required': 1, 'kept': 0, 'without.total': 1},
        'Unexpected R2 witness')

# No runtime assertion is accepted as a Lean axiom: observations are literal
# data. The small propositions below prove what those measured values imply.
defs = {
    'countBits': int(observed[0]['count']), 'libraryBits': int(observed[0]['library']),
    'targetBits': bits(float(exact)), 'outputBits': int(observed[0]['output']),
    'geneCount': row['count'], 'minCount': 10,
    'qualifying': row['qualified'], 'required': row['required'],
}
source = '-- Generated from fresh, cross-checked execution by verification/check.py.\nnamespace Observed\n'
source += ''.join(f'def {k} : Nat := {v}\n' for k, v in defs.items())
source += f'def kept : Bool := {"true" if row["kept"] else "false"}\nend Observed\n'
Path('Proofs/Observed.lean').write_text(source)
print('Checking Lean proofs and replaying their proof terms...', flush=True)
run(['lake', 'build', 'Proofs'], logfile='build.log')
require('depends on axioms' not in (OUT / 'build.log').read_text().replace('does not depend on any axioms', ''),
        'Unexpected theorem axiom dependencies')
lean_bin = Path(run(['lean', '--print-prefix']).strip()) / 'bin'
env = os.environ.copy()
env['LEAN_PATH'] = str(OUT) + ':' + run(['lake', 'env', 'printenv', 'LEAN_PATH']).strip()
export = run([lean_bin / 'leanexport', 'Proofs', '--',
              'Verification.r1_counterexample', 'Verification.r2_counterexample'], env=env)
(OUT / 'proofs.ndjson').write_text(export)
export_records = [json.loads(line) for line in export.splitlines()]
census = {kind: sum(kind in record for record in export_records)
          for kind in ['def', 'thm', 'inductive', 'axiom', 'opaque']}
census['bytes'] = len(export.encode())
census['lines'] = len(export_records)
(OUT / 'proof-census.json').write_text(json.dumps(census, indent=2) + '\n')


def nanoda(export_path, config_name):
    path = OUT / config_name
    path.write_text(json.dumps({
        'export_file_path': str(export_path), 'permitted_axioms': [],
        'unpermitted_axiom_hard_error': True, 'nat_extension': True,
        'string_extension': True, 'print_success_message': False,
    }, indent=2) + '\n')
    return [lean_bin / 'nanoda_bin', path]


run([lean_bin / 'leanchecker', '--from-export', OUT / 'proofs.ndjson'],
    env=env, logfile='kernel-cpp.log')
run([lean_bin / 'con-leche', '--verified', '--jobs=1', OUT / 'proofs.ndjson'],
    env=env, logfile='kernel-con-leche.log')
run([lean_bin / 'con-ron', '--verified', '--jobs=1', OUT / 'proofs.ndjson'],
    env=env, logfile='kernel-con-ron.log')
run(nanoda(OUT / 'proofs.ndjson', 'nanoda.json'), env=env, logfile='kernel-nanoda.log')
print('PASS: C++ Lean kernel, ConLeche, ConRon, and Nanoda replay (no permitted axioms)', flush=True)

# Test real invalid proof terms, not merely unparsable files or missing imports.
run(['lean', '-o', OUT / 'Forge.olean', 'Forge.lean'], env=env, cwd=ROOT / 'verification',
    logfile='forge-build.log')
forged = run([lean_bin / 'leanexport', 'Forge', '--', 'forgedFalse'], env=env)
(OUT / 'forged.ndjson').write_text(forged)
negative_commands = [
    ('cpp', [lean_bin / 'leanchecker', '--from-export', OUT / 'forged.ndjson']),
    ('con-leche', [lean_bin / 'con-leche', '--verified', '--jobs=1', OUT / 'forged.ndjson']),
    ('con-ron', [lean_bin / 'con-ron', '--verified', '--jobs=1', OUT / 'forged.ndjson']),
    ('nanoda', nanoda(OUT / 'forged.ndjson', 'nanoda-forged.json')),
]
for name, args in negative_commands:
    rejected = run(args, expect=1, env=env, logfile=f'reject-{name}.log')
    require(re.search(r'mismatch|not.?def.?eq|not definitionally equal|failed to check|'
                      r'assertion failed: self\.def_eq', rejected, re.I),
            f'{name}: no type checking rejection diagnostic:\n{rejected}')

run(['lean', '-o', OUT / 'Sorry.olean', 'Sorry.lean'], env=env, cwd=ROOT / 'verification',
    logfile='sorry-build.log')
(OUT / 'sorry.ndjson').write_text(run([lean_bin / 'leanexport', 'Sorry', '--', 'sorryFalse'], env=env))
rejected = run(nanoda(OUT / 'sorry.ndjson', 'nanoda-sorry.json'), expect=1,
               env=env, logfile='reject-sorry.log')
require('sorryAx' in rejected, 'Axiom audit did not identify sorryAx')
print('PASS: all four replay kernels reject forged False := True.intro; axiom audit rejects sorry', flush=True)

# Quantify every added file needed to interpret or reproduce the results.
review_files = ['Proofs.lean', 'Proofs/Claims.lean', 'Proofs/Observed.lean', 'verification/check.py',
                'verification/probe.wat', 'verification/run.mjs', 'verification/filter.R',
                'verification/inputs.sha256', 'verification/Forge.lean', 'verification/Sorry.lean']
with (OUT / 'sizes.tsv').open('w') as f:
    f.write('file\tlines\tbytes\n')
    for name in review_files:
        data = Path(name).read_bytes()
        f.write(f'{name}\t{len(data.splitlines())}\t{len(data)}\n')
(OUT / 'versions.txt').write_text('\n'.join([
    run(['lean', '--version']).strip(), run(['wasmtime', '--version']).strip(),
    run(['wasm-tools', '--version']).strip(), run(['node', '--version']).strip(),
    run(['Rscript', '--version']).strip(),
]))
(OUT / 'checkers.sha256').write_text(''.join(
    f'{hashlib.sha256((lean_bin / name).read_bytes()).hexdigest()}  {lean_bin / name}\n'
    for name in ['lean', 'leanexport', 'leanchecker', 'con-leche', 'con-ron', 'nanoda_bin']))
print('VERIFICATION PASSED: both README requirements have reproducible counterexamples.', flush=True)
