#!/usr/bin/env python3
"""Offline reproduction, full proof replay, and deliberately false certificates."""
import collections
import hashlib
import json
import pathlib
import subprocess
import sys

root = pathlib.Path(__file__).resolve().parent.parent
if pathlib.Path.cwd() != root:
    sys.exit('Run from the project directory')
out = pathlib.Path('.verification')
out.mkdir(exist_ok=True)


def run(cmd, log=None):
    if log is None:
        subprocess.run(cmd, check=True)
    else:
        with (out / log).open('w') as f:
            subprocess.run(cmd, check=True, stdout=f, stderr=subprocess.STDOUT)


for line in pathlib.Path('verification/SHA256SUMS').read_text().splitlines():
    digest, name = line.split('  ')
    assert hashlib.sha256(pathlib.Path(name).read_bytes()).hexdigest() == digest, name
print('PASS: shipped bytes and requirements match SHA256SUMS', flush=True)
run([sys.executable, 'verification/artifact.py', str(out)])
run(['Rscript', '--vanilla', 'verification/filter.R', str(out)])

# Force fresh frontend checking; do not accept an old project olean as evidence.
lib = pathlib.Path('.lake/build/lib/lean')
(lib / 'Proofs').mkdir(parents=True, exist_ok=True)
for source in ['Proofs/Certificate', 'Proofs']:
    run(['lake', 'env', 'lean', '-o', str(lib / (source + '.olean')), source + '.lean'])
prefix = pathlib.Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip())
bin_dir = prefix / 'bin'
targets = ['Certificate.' + n for n in
           ['bit_values', 'overflow_target', 'boundary_target', 'boundary_gap', 'boundary_error']]
run(['lake', 'env', str(bin_dir / 'leanexport'), 'Proofs', '--', *targets], 'proofs.ndjson')
rows = [json.loads(s) for s in (out / 'proofs.ndjson').read_text().splitlines()]
names = {0: ''}
for j in rows:
    if 'in' in j:
        v = j.get('str', j.get('num'))
        suffix = v['str'] if 'str' in v else str(v['i'])
        names[j['in']] = '.'.join(filter(None, [names[v['pre']], suffix]))
axioms = [names[j['axiom']['name']] for j in rows if 'axiom' in j]
assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}, axioms
assert set(targets) <= {names[j['thm']['name']] for j in rows if 'thm' in j}
decl_kinds = ['def', 'thm', 'opaque', 'axiom', 'inductive', 'quot']
counts = collections.Counter(k for j in rows for k in decl_kinds if k in j)
print(f'Proof export: {dict(counts)}; axioms: {axioms}', flush=True)


def checker_commands(stream):
    config = out / (stream.stem + '.nanoda.json')
    config.write_text(json.dumps({
        'export_file_path': str(stream), 'permitted_axioms':
        ['propext', 'Classical.choice', 'Quot.sound'],
        'unpermitted_axiom_hard_error': True, 'nat_extension': True,
        'string_extension': True, 'print_success_message': True}))
    return [('lean', [str(bin_dir / 'leanchecker'), '--from-export', str(stream)]),
            ('con-ron', [str(bin_dir / 'con-ron'), '--verified', '--jobs=2', str(stream)]),
            ('nanoda', [str(bin_dir / 'nanoda_bin'), str(config)])]


for name, cmd in checker_commands(out / 'proofs.ndjson'):
    run(cmd, name + '-valid.log')
    print(f'PASS: {name} replayed the complete proof dependency closure', flush=True)

# Append well-formed but ill-typed proof declarations. No missing imports,
# malformed JSON, untrusted axiom, or parser failure is used as a rejection test.
exprs = {j['ie']: j for j in rows if 'ie' in j}
name_ids = {v: k for k, v in names.items()}
level_one = next(j['il'] for j in rows if j.get('succ') == 0)


def false_certificate(which):
    extra = []
    next_expr = max(exprs) + 1
    memo = {json.dumps({k: v for k, v in j.items() if k != 'ie'}, sort_keys=True): i
            for i, j in exprs.items()}

    def expr(**fields):
        nonlocal next_expr
        key = json.dumps(fields, sort_keys=True)
        if key in memo:
            return memo[key]
        idx = next_expr
        next_expr += 1
        memo[key] = idx
        extra.append(dict(ie=idx, **fields))
        return idx

    def const(name, levels):
        return expr(const={'name': name_ids[name], 'us': levels})

    def app(fn, arg):
        return expr(app={'fn': fn, 'arg': arg})

    nat = const('Nat', [])
    zero = expr(natVal='0')
    refl_zero = app(app(const('Eq.refl', [level_one]), nat), zero)
    if which == 'False':
        proposition = const('False', [])
    else:
        proposition = app(app(app(const('Eq', [level_one]), nat), zero), expr(natVal='1'))
    name = max(names) + 1
    extra.append({'in': name, 'str': {'pre': 0, 'str': 'Forged_' + which}})
    extra.append({'thm': {'all': [name], 'levelParams': [], 'name': name,
                         'type': proposition, 'value': refl_zero}})
    path = out / ('false-' + which + '.ndjson')
    with path.open('w') as f:
        for j in rows + extra:
            f.write(json.dumps(j, separators=(',', ':')) + '\n')
    return path


for which in ['False', 'zero_eq_one']:
    for name, cmd in checker_commands(false_certificate(which)):
        p = subprocess.run(cmd, capture_output=True, text=True)
        log = p.stdout + p.stderr
        (out / (name + '-reject-' + which + '.log')).write_text(log)
        if name == 'nanoda':
            # Nanoda 0.4.19 asserts on a failed type equality. Other panics,
            # including parser panics, are NOT counted as successful rejection.
            assert p.returncode == 101 and 'src/tc.rs:' in log and \
                'assertion failed: self.def_eq(u, v)' in log, (which, p.returncode, log)
        else:
            assert p.returncode == 1, (name, which, p.returncode, log)
            assert any(s in log.lower() for s in ['type mismatch', 'rejected']), log
        print(f'PASS: {name} rejected forged proof of {which}', flush=True)

review = ['Proofs.lean', 'Proofs/Certificate.lean', 'check.sh',
          'verification/check.py', 'verification/artifact.py',
          'verification/run-wasm.mjs', 'verification/filter.R', 'verification/SHA256SUMS']
sizes = []
for name in review:
    data = pathlib.Path(name).read_bytes()
    sizes.append(f'{len(data.splitlines()):4} lines {len(data):6} bytes  {name}')
(out / 'review-size.txt').write_text('\n'.join(sizes) + '\n')
print('\n'.join(sizes))
print('SUCCESS: R1 and R2 counterexamples reproduced; three kernels accepted the certificates and rejected both false proofs.')
