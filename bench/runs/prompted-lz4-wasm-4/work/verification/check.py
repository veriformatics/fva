#!/usr/bin/env python3
"""Rebuild, replay, and negatively test every result; no network or source edits."""
import hashlib
import json
from pathlib import Path
import resource
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent.parent
LEAN_BIN = Path(shutil.which('lean')).resolve().parent
OUT = ROOT / '.lake' / 'verification'
OUT.mkdir(parents=True, exist_ok=True)
resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def run(args, *, failure=None, save=None, show=False):
    p = subprocess.run([str(x) for x in args], cwd=ROOT, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    message = p.stdout + p.stderr
    if save is not None:
        save.write_text(p.stdout)
    if failure is None:
        assert p.returncode == 0, f'{args}: exit {p.returncode}\n{message}'
    else:
        assert p.returncode != 0, f'FALSE RESULT ACCEPTED: {args}'
        for text in failure:
            assert text in message, f'Wrong rejection for {args}:\n{message}'
    if show:
        print(message.strip(), flush=True)
    return p.stdout, message


# Pin the artifact and the two documents being interpreted, before execution.
for file, size, digest in [
    ('lz4-block-codec.wasm', 1226,
     '4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf'),
    ('lz4_Block_format.md', 10683,
     'dce3c34a8738c44ed1dffb48c73e30297fca98ba7881408dc228865912c9a42e'),
    ('README.md', 1798,
     '84232202637378126a384cc564d46f09b3ce750aa580c37ee91a4661a0417814'),
]:
    data = (ROOT / file).read_bytes()
    assert len(data) == size and hashlib.sha256(data).hexdigest() == digest, file
print('Pinned artifact and requirements: OK', flush=True)
run(['wasm-tools', 'validate', 'lz4-block-codec.wasm'])
_, dump = run(['wasm-tools', 'dump', 'lz4-block-codec.wasm'], save=OUT / 'artifact.dump')
assert any('0x32c | 2d 00 00' in line and 'i32_load8_u' in line
           for line in dump.splitlines())

# Direct execution in two unrelated engines. Wasmtime imports the unchanged module.
run(['node', 'verification/runtime.mjs'], show=True)
run(['node', 'verification/runtime.mjs', '--false'], failure=['AssertionError', '1 !== 13'])
harness = OUT / 'harness.wasm'
run(['wasm-tools', 'parse', 'verification/harness.wat', '-o', harness])
base = ['wasmtime', 'run', '-C', 'cache=n', '--preload',
        'codec=lz4-block-codec.wasm', '--invoke']
for export, expected in [('r1', '13'), ('r2', '1')]:
    stdout, _ = run(base + [export, harness])
    assert stdout.strip() == expected, (export, stdout)
    print(f'Wasmtime {export.upper()}: {expected}, all memory assertions passed', flush=True)
_, trap = run(base + ['r3', harness],
              failure=['0x32c', 'address 0x10000', 'size 0x10000',
                       'out of bounds memory access'])
(OUT / 'r3-trap.txt').write_text(trap)
run(base + ['falseAssertion', harness], failure=['unreachable'])
print('Wasmtime R3: load at binary offset 0x32c traps at address 65536', flush=True)
print('Both engines reject deliberately false runtime assertions: OK', flush=True)

# Always compile the actual sources; do not rely on cached project proof objects.
lib = ROOT / '.lake' / 'build' / 'lib' / 'lean'
(lib / 'Proofs').mkdir(parents=True, exist_ok=True)
run(['lake', 'env', 'lean', 'Proofs/Format.lean', '-o', lib / 'Proofs/Format.olean'])
run(['lake', 'env', 'lean', 'Proofs.lean', '-o', lib / 'Proofs.olean'])
run(['lake', 'env', 'lean', 'verification/KernelNegative.lean'],
    failure=['(kernel) declaration type mismatch', '0 = 0', '0 = 1'])
print('Lean: all proofs accepted; direct kernel submission of false proof rejected', flush=True)

roots = ['LZ4.' + x for x in ['r1_invalid', 'r2_content', 'r2_valid',
         'r2_wrong_length', 'r3_empty_valid', 'r3_outside', 'kernelCanary']]
export = OUT / 'proofs.jsonl'
run(['lake', 'env', 'leanexport', 'Proofs.Format', '--'] + roots, save=export)
records = [json.loads(line) for line in export.read_text().splitlines()]
names, exprs, theorems, axioms = {0: ''}, {}, {}, []
for record in records:
    if 'in' in record:
        d = record.get('str', record.get('num'))
        component = d['str'] if 'str' in d else str(d['i'])
        prefix = names[d['pre']]
        names[record['in']] = prefix + ('.' if prefix else '') + component
    if 'ie' in record:
        exprs[record['ie']] = record
    if 'thm' in record:
        theorems[names[record['thm']['name']]] = record['thm']
    if 'axiom' in record:
        axioms.append(names[record['axiom']['name']])
assert set(roots) <= theorems.keys()
assert set(axioms) <= {'propext'}, axioms
kinds = ['def', 'thm', 'opaque', 'axiom', 'inductive', 'quot']
census = {k: sum(k in r for r in records) for k in kinds}
print(f'Export closure: {sum(census.values())} declaration records, '
      f'{export.stat().st_size} bytes; axioms={axioms}; {census}', flush=True)

# Preserve the complete dependency closure, replacing just the canary's type
# Eq Nat 0 0 with Eq Nat 0 1. Its Eq.refl 0 proof body is unchanged.
canary = theorems['LZ4.kernelCanary']
old_type = exprs[canary['type']]
one = next(i for i, e in exprs.items() if e.get('natVal') == '1')
new_id = max(exprs) + 1
new_type = {'ie': new_id, 'app': {**old_type['app'], 'arg': one}}
bad_export = OUT / 'false-proof.jsonl'
with bad_export.open('w') as f:
    for record in records:
        if record.get('thm') is canary:
            f.write(json.dumps(new_type) + '\n')
            record = {'thm': {**canary, 'type': new_id}}
        f.write(json.dumps(record) + '\n')

config = {'permitted_axioms': ['propext'], 'unpermitted_axiom_hard_error': True,
          'nat_extension': True, 'string_extension': True,
          'pp_declars': roots, 'pp_to_stdout': True, 'print_success_message': True}
for name, stream, false in [('good', export, False), ('bad', bad_export, True)]:
    config['export_file_path'] = str(stream)
    config_path = OUT / f'nanoda-{name}.json'
    config_path.write_text(json.dumps(config))
    _, result = run([LEAN_BIN / 'nanoda_bin', config_path],
                    failure=['assertion failed: self.def_eq'] if false else None,
                    show=not false)
    if not false:
        assert 'no errors' in result
    _, result = run([LEAN_BIN / 'con-ron', '--verified', '--jobs=1', stream],
                    failure=['rejected: type mismatch in theorem', 'LZ4.kernelCanary']
                    if false else None, show=not false)
    if not false:
        assert 'accepted' in result
print('Nanoda and con-ron: replay accepted; forged 0 = 1 proof rejected: OK', flush=True)

files = ['Proofs/Format.lean', 'Proofs.lean', 'verification/check.py',
         'verification/runtime.mjs', 'verification/harness.wat',
         'verification/KernelNegative.lean']
print('Review surface (full files, including comments/blank lines):', flush=True)
for file in files:
    data = (ROOT / file).read_bytes()
    print(f'  {file}: {len(data.splitlines())} lines, {len(data)} bytes', flush=True)
print('PASS: R1, R2, R3 REFUTED on the pinned shipped artifact; '
      'three proof kernels and two runtime engines checked, including negative controls.', flush=True)
