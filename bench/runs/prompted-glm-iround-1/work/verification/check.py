#!/usr/bin/env python3
"""Reproduce the artifact counterexample, fresh proofs, and rejection controls."""
import copy
import hashlib
import json
import math
import os
from pathlib import Path
import re
import struct
import subprocess

ROOT = Path(__file__).resolve().parent.parent
os.chdir(ROOT)
OUT = ROOT / '.verification'
OUT.mkdir(exist_ok=True)
(OUT / 'Proofs').mkdir(exist_ok=True)
ENV = dict(os.environ, LEAN_PATH=str(OUT) + os.pathsep + os.environ.get('LEAN_PATH', ''))
LEAN_BIN = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip()) / 'bin'
KERNELS = {
    'Lean': ([str(LEAN_BIN / 'leanchecker'), '--from-export'], 'accepts the solution'),
    'con-leche': ([str(LEAN_BIN / 'con-leche'), '--verified', '--jobs=2'], 'accepted'),
    'con-ron': ([str(LEAN_BIN / 'con-ron'), '--verified', '--jobs=2'], 'accepted'),
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def run(args, log):
    p = subprocess.run([str(a) for a in args], env=ENV, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    (OUT / log).write_text(p.stdout + p.stderr)
    require(p.returncode == 0, f'{args[0]} failed; see .verification/{log}')
    return p.stdout


def export(module, roots, target):
    text = run([LEAN_BIN / 'leanexport', module, '--', *roots], target)
    return [json.loads(line) for line in text.splitlines()]


def names(rows):
    result = {0: ''}
    for r in rows:
        if 'in' in r:
            node = r.get('str', r.get('num'))
            tail = node.get('str', str(node.get('i', '')))
            pre = result[node['pre']]
            result[r['in']] = pre + ('.' if pre else '') + tail
    return result


def replay(path, label, reject=False):
    for name, (command, success) in KERNELS.items():
        p = subprocess.run([*command, str(path)], env=ENV, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        diagnostic = p.stdout + p.stderr
        (OUT / f'{label}-{name}.log').write_text(diagnostic)
        if reject:
            require(p.returncode == 1 and 'type mismatch' in diagnostic.lower(),
                    f'{name} did not explicitly reject {label}; inspect its log')
        else:
            require(p.returncode == 0 and success in diagnostic,
                    f'{name} did not accept {label}; inspect its log')
        print(f'{name}: {"REJECTED" if reject else "ACCEPTED"} {label}', flush=True)


artifact = Path('glm-iround.wasm').read_bytes()
require(len(artifact) == 66 and hashlib.sha256(artifact).hexdigest() ==
        'eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a',
        'Artifact differs from README: stop rather than check another program')
run(['wasm-tools', 'validate', 'glm-iround.wasm'], 'artifact-validate.log')
run(['wasm-tools', 'print', 'glm-iround.wasm'], 'artifact.wat')
wat = Path('verification/witness.wat').read_text()
bits, = re.findall(r'i64.const\s+(0x[0-9a-f]+)', wat)
value, = struct.unpack('>d', int(bits, 16).to_bytes(8, 'big'))
require(math.isfinite(value), 'Witness must be finite')
numerator, denominator = value.as_integer_ratio()
require((numerator, denominator) == (9007199254740991, 18014398509481984),
        'Witness bits no longer encode the documented exact rational')
run(['wasm-tools', 'parse', 'verification/witness.wat', '-o', OUT / 'witness.wasm'],
    'wrapper-build.log')
observed = run(['wasmtime', 'run', '-C', 'cache=n', '--preload',
                'artifact=glm-iround.wasm', '--invoke', 'run', OUT / 'witness.wasm'],
               'execution.log').strip()
require(observed == '1', 'Counterexample not reproduced')
print(f'Artifact: {len(artifact)} bytes, expected SHA-256; input {bits}, output {observed}',
      flush=True)

# Freshly compile, then export the theorem specialized to the actual observation.
run(['lean', '-o', OUT / 'Proofs/Counterexample.olean', 'Proofs/Counterexample.lean'],
    'compile-proof.log')
observation = f'''import Proofs.Counterexample
namespace Observation
theorem r1_failure :
    let num : Int := {numerator}
    let den : Int := {denominator}
    let output : Int := {observed}
    0 < den ∧ 0 ≤ num ∧ num ≤ 2147483647 * den ∧
      ¬ Verification.Nearest num den output :=
  ⟨Verification.r1_counterexample.1, Verification.r1_counterexample.2.1,
    Verification.r1_counterexample.2.2.1, Verification.r1_counterexample.2.2.2.2⟩
end Observation
#print axioms Observation.r1_failure
'''
(OUT / 'Observation.lean').write_text(observation)
run(['lean', '-o', OUT / 'Observation.olean', OUT / 'Observation.lean'], 'compile-binding.log')
proof = export('Observation', ['Observation.r1_failure'], 'proof.ndjson')
lookup = names(proof)
axioms = {lookup[r['axiom']['name']] for r in proof if 'axiom' in r}
require(not axioms,
        f'Unexpected axioms: {axioms}')
replay(OUT / 'proof.ndjson', 'proof')

# Well-formed controls: keep the same proof of 0=0, change only its claimed type.
run(['lean', '-o', OUT / 'Controls.olean', 'verification/Controls.lean'], 'compile-controls.log')
controls = export('Controls', ['Control.good', 'Control.badEquality', 'Control.badFalse'],
                  'controls-original.ndjson')
lookup = names(controls)
good, = [r for r in controls if 'thm' in r and lookup[r['thm']['name']] == 'Control.good']
controls.remove(good)
for label, bad in [('valid-control', None), ('false-equality', 'Control.badEquality'),
                   ('false-proposition', 'Control.badFalse')]:
    final = copy.deepcopy(good)
    if bad:
        claim, = [r['def']['value'] for r in controls if 'def' in r and
                  lookup[r['def']['name']] == bad]
        final['thm']['type'] = claim
    path = OUT / f'{label}.ndjson'
    path.write_text(''.join(json.dumps(r) + '\n' for r in [*controls, final]))
    replay(path, label, reject=bad is not None)

# Report conservative full dependency sizes, including proof dependencies.
counts = {kind: sum(kind in r for r in proof)
          for kind in ['def', 'thm', 'axiom', 'opaque', 'inductive', 'quot']}
(OUT / 'dependency-inventory.json').write_text(json.dumps({
    'records': counts, 'axioms': sorted(axioms),
    'export_bytes': (OUT / 'proof.ndjson').stat().st_size,
    'declarations': sorted(names(proof)[r[k]['name']] for r in proof
                           for k in ['def', 'thm', 'axiom', 'opaque', 'quot'] if k in r),
}, indent=2) + '\n')
print('Dependency records:', counts, flush=True)
print('PASS: R1 is FALSE; exact artifact counterexample, proofs, and rejection controls checked.')
