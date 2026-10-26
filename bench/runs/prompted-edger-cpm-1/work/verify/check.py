#!/usr/bin/env python3
"""Offline, fail-closed replay of counterexamples and arithmetic certificates."""
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import struct
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.verification'
os.chdir(ROOT)
OUT.mkdir(exist_ok=True)


def run(args, log, expect=0):
    p = subprocess.run([str(a) for a in args], text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=300)
    (OUT / log).write_text(p.stdout)
    if p.returncode != expect:
        raise RuntimeError(f'{args}: exit {p.returncode}\n{p.stdout}')
    return p.stdout


# Freeze all supplied requirements, implementation, and documentation files.
for path, digest in json.loads(Path('verify/artifacts.json').read_text()).items():
    if hashlib.sha256(Path(path).read_bytes()).hexdigest() != digest:
        raise RuntimeError(f'artifact changed: {path}')
print('PASS: original artifact/source/documentation hashes', flush=True)

# Generate only the host imports from the disassembly. The original edgeR.so
# itself is preloaded unchanged, rather than reassembled from this text.
wat = run(['wasm-tools', 'print', 'edgeR.so'], 'edgeR.wat')
modules = {}
for line in wat.splitlines():
    match = re.fullmatch(r'  \(import "([^"]+)" "([^"]+)" (.*)\)', line)
    if not match:
        continue
    module, name, body = match.groups()
    lines = modules.setdefault(module, [])
    if body.startswith('(func '):
        sig = ' '.join(re.findall(r'\((?:param|result) [^)]*\)', body))
        code = 'unreachable'
        if name == 'R_chk_free':
            code = ''
        elif name == 'R_chk_calloc':
            code = ('(local i32) global.get $heap local.set 2 global.get $heap '
                    'local.get 0 local.get 1 i32.mul i32.add i32.const 7 i32.add '
                    'i32.const -8 i32.and global.set $heap local.get 2 i32.const 0 '
                    'local.get 0 local.get 1 i32.mul memory.fill local.get 2')
        lines.append(f'(func (export "{name}") {sig} {code})')
    elif body.startswith('(global '):
        typ = '(mut i32)' if '(mut i32)' in body else 'i32'
        value = 65536 if name == '__stack_pointer' else 0
        lines.append(f'(global (export "{name}") {typ} (i32.const {value}))')
    elif body.startswith('(memory '):
        lines.append(f'(memory (export "{name}") 16)')
    elif body.startswith('(table '):
        lines.append(f'(table (export "{name}") 9 funcref)')
    else:
        raise RuntimeError(f'unhandled import {body}')
preloads = []
for module, lines in modules.items():
    if module == 'env':
        lines.append('(global $heap (mut i32) (i32.const 262144))')
    path = OUT / f'{module}.wat'
    path.write_text('(module\n' + '\n'.join(lines) + '\n)\n')
    preloads += ['--preload', f'{module}={path}']
preloads += ['--preload', 'artifact=edgeR.so']

# Each runtime executes the exact shipped artifact. Neither host supplies CPM.
cases = [('zero', 0., 36., 0), ('ordinary', 20., 1e6, 0x4034000000000000),
         ('boundary', 20., 36., 0x4120f4471c71c71c),
         ('overflow', 2.**1023, 2.**1023, 0x7ff0000000000000)]
for label, count, library, expected_bits in cases:
    (OUT / 'input.bin').write_bytes(struct.pack('<dd', count, library))
    run(['node', 'verify/runtime.mjs', '1', '1', OUT/'input.bin', OUT/'output.bin'],
        f'node-{label}.log')
    node_bits, = struct.unpack('<Q', (OUT / 'output.bin').read_bytes())
    text = run(['wasmtime', 'run', '-C', 'cache=n', *preloads, '--invoke', 'run',
                'verify/driver.wat', repr(count), repr(library)], f'wasmtime-{label}.log')
    wasm_bits = int(text.strip().splitlines()[-1]) & ((1 << 64) - 1)
    if not node_bits == wasm_bits == expected_bits:
        raise RuntimeError(f'{label}: runtime mismatch: {node_bits:x}, {wasm_bits:x}')
    print(f'PASS: Node + Wasmtime {label}: {expected_bits:016x}', flush=True)
print(run(['Rscript', '--vanilla', 'verify/filter.R'], 'filter.log').strip(), flush=True)

# Rebuild our own modules from source, never accepting cached local oleans.
shutil.rmtree('.lake/build', ignore_errors=True)
print(run(['lake', 'build', 'Proofs', 'Proofs.Controls'], 'build.log').strip(), flush=True)
sysroot = Path(run(['lean', '--print-prefix'], 'sysroot.log').strip())
exporter = sysroot / 'bin/leanexport'
checkers = [('Lean default kernel', [sysroot/'bin/leanchecker', '--from-export']),
            ('con-ron Rust kernel', [sysroot/'bin/con-ron', '--verified']),
            ('Nanoda Rust kernel', [sysroot/'bin/nanoda_bin'])]


def export(module, names, filename):
    text = run(['lake', 'env', exporter, module, '--', *names], filename)
    records = [json.loads(line) for line in text.splitlines()]
    # No axiom whitelist, compiler oracle, sorry, opaque or unsafe declarations.
    for r in records:
        if 'axiom' in r or 'opaque' in r:
            raise RuntimeError('axiom/opaque in certificate')
        if 'def' in r and r['def']['safety'] != 'safe':
            raise RuntimeError('unsafe definition in certificate')
    return records


def checker(kernel, command, filename, reject=False):
    if kernel.startswith('Nanoda'):
        cfg = OUT / 'nanoda.json'
        cfg.write_text(json.dumps({'export_file_path': str(OUT/filename),
                                  'permitted_axioms': [], 'unpermitted_axiom_hard_error': True,
                                  'nat_extension': True, 'string_extension': True,
                                  'print_success_message': False}))
        args = [*command, cfg]
    else:
        args = [*command, OUT/filename]
    log = f'{filename}-{kernel.split()[0]}.log'
    expected_exit = (101 if kernel.startswith('Nanoda') else 1) if reject else 0
    output = run(args, log, expect=expected_exit)
    if reject:
        # Require a type-checking rejection, not a parse error or missing file.
        marker = 'src/tc.rs:' if kernel.startswith('Nanoda') else 'type mismatch'
        if marker not in output:
            raise RuntimeError(f'{kernel} did not reject in its type checker: {output}')
    print(f'PASS: {kernel} {"rejects" if reject else "accepts"} {filename}', flush=True)


def decode_names(records):
    names = {0: ''}
    for r in records:
        if 'in' in r:
            node = r.get('str', r.get('num'))
            names[r['in']] = '.'.join(filter(None, [names[node['pre']],
                                      str(node.get('str', node.get('i')))]))
    return names


roots = ['Evidence.r1_witness', 'Evidence.r2_boundary_witness', 'Evidence.r2_tolerance_witness']
records = export('Proofs.Counterexamples', roots, 'evidence.ndjson')
names = decode_names(records)
if not set(roots) <= {names[r['thm']['name']] for r in records if 'thm' in r}:
    raise RuntimeError('missing certificate theorem')
controls = export('Proofs.Controls', ['Controls.valid', 'Controls.falseEquality',
                                   'Controls.falseOrder'], 'controls.ndjson')
for kernel, command in checkers:
    checker(kernel, command, 'evidence.ndjson')
    checker(kernel, command, 'controls.ndjson')

# Syntactically valid streams asserting 0=1 and 1<0 with an Eq.refl 0 proof.
# Move the changed theorem after all expressions to avoid forward references.
names = decode_names(controls)
seed = next(r for r in controls if 'thm' in r and names[r['thm']['name']] == 'Controls.valid')
for claim in ['falseEquality', 'falseOrder']:
    changed = copy.deepcopy(seed)
    changed['thm']['type'] = next(r['def']['value'] for r in controls if 'def' in r
                                and names[r['def']['name']] == 'Controls.'+claim)
    filename = claim + '.ndjson'
    (OUT/filename).write_text(''.join(json.dumps(r)+'\n' for r in controls if r is not seed)
                             + json.dumps(changed)+'\n')
    for kernel, command in checkers:
        checker(kernel, command, filename, reject=True)

# Conservative review size: entire proof closure, including proof terms.
declarations = sum(any(k in r for k in ['def', 'thm', 'inductive', 'axiom', 'opaque']) for r in records)
print(f'Proof closure: {declarations} declaration records; '
      f'{len((OUT/"evidence.ndjson").read_bytes())} bytes', flush=True)
for path in ['Proofs/Counterexamples.lean', 'Proofs/Controls.lean', 'verify/check.py',
             'verify/runtime.mjs', 'verify/driver.wat', 'verify/filter.R', 'verify/artifacts.json']:
    data = Path(path).read_bytes()
    print(f'Review size {path}: {len(data.splitlines())} lines, {len(data)} bytes', flush=True)
print('VERIFICATION PASS: both requirements refuted; all three kernels accepted '
      'the certificates and rejected both false proofs.', flush=True)
