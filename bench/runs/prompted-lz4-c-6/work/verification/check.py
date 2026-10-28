#!/usr/bin/env python3
"""One offline check: extraction, proof replay, negative controls, and runtime tests."""
import json
from pathlib import Path
import shutil
import subprocess

OUT = Path('verification/out')
OUT.mkdir(exist_ok=True)
ROOTS = ['Verification.zero_capacity', 'Verification.zero_source_size']
ALLOWED = {'propext', 'Quot.sound'}
prefix = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip())

def tool(name):
    path = shutil.which(name) or str(prefix / 'bin' / name)
    assert Path(path).is_file(), f'Missing tool: {name}'
    return path

def run(args, output=None):
    print('+ ' + ' '.join(map(str, args)), flush=True)
    if output:
        with Path(output).open('w') as stream:
            subprocess.run(list(map(str, args)), stdout=stream, check=True)
    else:
        subprocess.run(list(map(str, args)), check=True)

def audit(path, roots):
    names, axioms, theorems = {0: ''}, set(), set()
    for line in Path(path).open():
        d = json.loads(line)
        if 'in' in d:
            item = d.get('str', d.get('num'))
            assert item is not None
            names[d['in']] = (names[item['pre']] + '.' if item['pre'] else '') + str(item.get('str', item.get('i')))
        if 'axiom' in d:
            axioms.add(names[d['axiom']['name']])
        if 'thm' in d:
            theorems.add(names[d['thm']['name']])
    assert axioms <= ALLOWED, f'Unapproved axioms: {axioms - ALLOWED}'
    assert set(roots) <= theorems, 'Missing target proof in export'
    print(f'Export audit: target proofs present; axioms={sorted(axioms)}', flush=True)

def nanoda(export, label, pretty=False):
    config = {'export_file_path': str(export.resolve()), 'permitted_axioms': sorted(ALLOWED),
              'unpermitted_axiom_hard_error': True, 'nat_extension': True,
              'string_extension': True, 'print_success_message': True}
    if pretty:
        (OUT / 'statements.txt').write_text('')
        config.update(pp_declars=ROOTS, pp_output_path=str((OUT / 'statements.txt').resolve()))
    path = OUT / f'{label}.json'
    path.write_text(json.dumps(config, indent=2) + '\n')
    return [tool('nanoda_bin'), str(path)]

def reject(args, label, needle):
    result = subprocess.run(list(map(str, args)), text=True, capture_output=True)
    log = result.stdout + result.stderr
    (OUT / f'{label}.log').write_text(log)
    assert result.returncode != 0, f'FALSE PROOF ACCEPTED: {label}'
    assert needle in log, f'{label} failed for an unrelated reason: {log[:2000]}'
    assert any(s in log.lower() for s in ['mismatch', 'not def', 'not equal', 'typechecker error', 'assertion failed: self.def_eq']), log
    print(f'Negative control: {label} rejected the false proof (exit {result.returncode})', flush=True)

run(['python3', 'verification/extract.py', '--check'])
run(['wasm-tools', 'validate', 'lz4-c.wasm'])
run(['lake', 'clean', 'proofs'])
run(['lake', 'build'])
run(['lake', 'env', 'leanchecker', 'Proofs'])
export = OUT / 'proofs.ndjson'
run(['lake', 'env', tool('leanexport'), 'Proofs', '--', *ROOTS], export)
audit(export, ROOTS)
run([tool('con-ron'), '--verified', '--jobs=2', export])
run(nanoda(export, 'positive', pretty=True))
assert all(name in (OUT / 'statements.txt').read_text() for name in ROOTS)

# The frontend deliberately emits malformed proof terms, bypassing its kernel only
# for these isolated fixtures. Exactly the same replay commands must reject both.
negative_olean = Path('.lake/build/lib/lean/verification/negative')
negative_olean.mkdir(parents=True, exist_ok=True)
for fixture, name in [('Bad', 'deliberatelyFalse'), ('BadEq', 'deliberatelyFalseEquality')]:
    module = f'verification.negative.{fixture}'
    run(['lake', 'env', 'lean', '-o', negative_olean / f'{fixture}.olean',
         f'verification/negative/{fixture}.lean'])
    reject(['lake', 'env', 'leanchecker', module], f'{fixture}-leanchecker', name)
    bad_export = OUT / f'{fixture}.ndjson'
    run(['lake', 'env', tool('leanexport'), module, '--', name], bad_export)
    audit(bad_export, [name])
    reject([tool('con-ron'), '--verified', '--jobs=2', bad_export], f'{fixture}-con-ron', name)
    reject(nanoda(bad_export, fixture), f'{fixture}-nanoda', 'self.def_eq')

run(['python3', 'verification/instrument.py'])
run(['node', 'verification/test.mjs'])
# Report source sizes without excluding comments, whitespace, or generated data.
files = ['Proofs.lean', 'Proofs/Wasm.lean', 'Proofs/Artifact.lean', 'Proofs/Cases.lean',
         'verification/extract.py', 'verification/check.py', 'verification/instrument.py',
         'verification/test.mjs', 'verification/negative/Bad.lean',
         'verification/negative/BadEq.lean', 'check.sh']
rows = []
for file in files:
    data = Path(file).read_bytes()
    rows.append(f'{file}: {data.count(bytes([10]))} lines, {len(data)} bytes')
(OUT / 'sizes.txt').write_text('\n'.join(rows) + '\n')
print('\n'.join(rows))
print('CHECK PASSED: two scoped theorems replayed in three kernels; all negative controls and runtime tests passed.')
print('PARTIAL RESULT: R1, R2, and R3 remain unproved for the general decoding paths.')
