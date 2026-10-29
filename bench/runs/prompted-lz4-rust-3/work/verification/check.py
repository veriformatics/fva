#!/usr/bin/env python3
"""One offline command. Exit 0 certifies only the partial results in VERIFICATION.md."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
os.chdir(ROOT)
OUT = ROOT / '.verification'
OUT.mkdir(exist_ok=True)
LEAN_BIN = Path(shutil.which('lean')).resolve().parent
TARGETS = ['Artifact.decoded_artifact', 'Results.empty_input',
           'Results.interface_cases', 'Results.expected_cases',
           'Results.r1_cases', 'Results.r2_cases', 'Results.r3_cases',
           'Results.one_byte', 'Results.one_byte_format']

def run(label, args, *, failure=False, output=None, rejection_code=1):
    print(label, flush=True)
    p = subprocess.run([str(a) for a in args], stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=900)
    (OUT / (label.replace(' ', '_').replace('/', '_')+'.log')).write_bytes(p.stdout)
    if output:
        Path(output).write_bytes(p.stdout)
    if failure:
        assert p.returncode == rejection_code, (label, p.returncode, p.stdout.decode(errors='replace')[-3000:])
    elif p.returncode != 0:
        raise RuntimeError(f'{label}: exit {p.returncode}\n{p.stdout.decode(errors="replace")[-5000:]}')
    return p.stdout.decode()

def stream_names(rows):
    names = {0: ''}
    for r in rows:
        if 'in' in r:
            k = 'str' if 'str' in r else 'num'
            x = r[k]
            names[r['in']] = '.'.join(filter(None, [names[x['pre']],
                                                  x['str'] if k == 'str' else str(x['i'])]))
    return names

def audit(path, targets):
    rows = [json.loads(s) for s in path.read_text().splitlines()]
    names = stream_names(rows)
    axioms = {names[r['axiom']['name']] for r in rows if 'axiom' in r}
    assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}, axioms
    found = {names[r['thm']['name']] for r in rows if 'thm' in r}
    assert set(targets) <= found, set(targets)-found
    print('export axioms:', sorted(axioms), flush=True)
    return rows

def nanoda(label, path, failure=False):
    cfg = OUT / (label+'.json')
    cfg.write_text(json.dumps({'export_file_path': str(path),
        'permitted_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'unpermitted_axiom_hard_error': True, 'nat_extension': True,
        'string_extension': True, 'print_success_message': True}))
    result = run(label, [LEAN_BIN/'nanoda_bin', cfg], failure=failure, rejection_code=101)
    if failure:
        assert 'panicked at src/tc.rs:955:71:' in result, result
        assert 'assertion failed: self.def_eq(u, v)' in result, result
    assert ('no typechecker errors' in result) != failure, result[-2000:]

def conron(label, path, failure=False):
    result = run(label, [LEAN_BIN/'con-ron', '--verified', path], failure=failure)
    assert ('accepted' in result) != failure, result[-2000:]

run('artifact link', [sys.executable, 'verification/artifact.py'])
run('wasm validation', ['wasm-tools', 'validate', 'lz4-flex.wasm'])
# Rebuild the local project; leave the prebuilt external Mathlib packages intact.
shutil.rmtree(ROOT/'.lake/build', ignore_errors=True)
run('Lean fresh build', ['lake', 'build'])
proofs = OUT/'proofs.ndjson'
run('export proofs', ['lake', 'env', 'leanexport', 'Proofs', '--', *TARGETS], output=proofs)
audit(proofs, TARGETS)
nanoda('nanoda proofs', proofs)
conron('conron proofs', proofs)

# Compile a true reflexivity proof; independent checkers must first accept it.
run('build challenge', ['lake', 'env', 'lean', '-o', OUT/'Challenge.olean',
                        'verification/Challenge.lean'])
# The import path is explicit, so the just-built fixture is the one exported.
fixture_env = os.environ.get('LEAN_PATH', '')
os.environ['LEAN_PATH'] = str(OUT) + (os.pathsep+fixture_env if fixture_env else '')
challenge = OUT/'challenge.ndjson'
run('export challenge', ['lake', 'env', 'leanexport', 'Challenge', '--', 'challenge'], output=challenge)
rows = audit(challenge, ['challenge'])
nanoda('nanoda true control', challenge)
conron('conron true control', challenge)
# Well-formed export of the claim 0=1, with the original proof Eq.refl 0.
exprs = {r['ie']: r for r in rows if 'ie' in r}
next_id = max(exprs)+1
for i,r in enumerate(rows):
    if 'thm' in r:
        thm = r['thm']
        outer = exprs[thm['type']]['app']
        new = [{'ie': next_id, 'natVal': '1'},
               {'ie': next_id+1, 'app': {'fn': outer['fn'], 'arg': next_id}}]
        thm['type'] = next_id+1
        rows[i:i] = new
        break
false = OUT/'false.ndjson'
false.write_text(''.join(json.dumps(r)+'\n' for r in rows))
nanoda('nanoda false control', false, failure=True)
conron('conron false control', false, failure=True)
run('Lean false control', ['lake', 'env', 'lean', 'verification/FalseProof.lean'], failure=True)
mutant = OUT/'mutant.ndjson'
run('mutate actual proof', [sys.executable, 'verification/negative.py', proofs, mutant, 'Results.r1_cases'])
nanoda('nanoda mutated proof', mutant, failure=True)
conron('conron mutated proof', mutant, failure=True)

cases = OUT/'cases.json'
run('export runtime cases', ['lake', 'env', 'lean', '--run', 'verification/ExportCases.lean'], output=cases)
run('V8 original binary', ['node', 'verification/runtime.mjs', cases])
wast = OUT/'cases.wast'
run('make Wasmtime tests', [sys.executable, 'verification/make_wast.py', cases, wast])
run('Wasmtime original binary', ['wasmtime', 'wast', '-C', 'cache=n', wast])
bad_cases = json.loads(cases.read_text())
bad_cases[0]['result'] = 0
bad = OUT/'bad-cases.json'
bad.write_text(json.dumps(bad_cases))
run('V8 false control', ['node', 'verification/runtime.mjs', bad], failure=True)
bad_wast = OUT/'bad-cases.wast'
run('make false runtime test', [sys.executable, 'verification/make_wast.py', bad, bad_wast])
run('Wasmtime false control', ['wasmtime', 'wast', '-C', 'cache=n', bad_wast], failure=True)

files = ['Proofs/Syntax.lean', 'Proofs/Wasm.lean', 'Proofs/Spec.lean',
         'Proofs/Results.lean', 'Proofs/OneByte.lean', 'verification/artifact.py',
         'verification/check.py', 'verification/negative.py',
         'verification/ExportCases.lean', 'verification/runtime.mjs',
         'verification/make_wast.py', 'verification/Challenge.lean', 'verification/FalseProof.lean']
size = {p: {'lines':len(Path(p).read_text().splitlines()), 'bytes':Path(p).stat().st_size} for p in files}
(OUT/'review-size.json').write_text(json.dumps(size, indent=2)+'\n')
print('PASS: partial artifact proofs replayed; false proofs rejected; both runtimes agree.')
print('R1, R2 and R3 for arbitrary inputs remain UNPROVED. See VERIFICATION.md.')
