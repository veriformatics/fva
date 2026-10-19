#!/usr/bin/env python3
"""Offline, fail-closed reproduction, proof replay, and adversarial controls."""
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / '.verification'
MODULES = OUT / 'lean'
BASELINE = {
    'avg_floor.c': '8ddea065a9c9412f7b1ccd818ae22c04578dbe34ff9470c2b192df417777f5e0',
    'avg_floor.wasm': '551d0f840db799ed5ff513d8c47b0d2eaf2f01f662ff408e8f5df41b152c93ba',
    'README.md': '30efefdb54600854f010e44bca79f366d98285e8884c168838e398406d4e93e8',
}
ROOTS = ['AvgFloor.' + n for n in (
    'floor_spec', 'decoded', 'semantics', 'correct_iff', 'fails_on_overflow',
    'positive_counterexample', 'negative_counterexample', 'not_R1', 'not_R2')]
AXIOMS = {'propext', 'Quot.sound', 'Classical.choice'}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def run(label, command, *, env=None, reject=False, stdout=None):
    log = OUT / (label + '.log')
    with log.open('w') as errors:
        if stdout is None:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=errors,
                                    stderr=subprocess.STDOUT, timeout=180)
        else:
            with stdout.open('w') as output:
                result = subprocess.run(command, cwd=ROOT, env=env, stdout=output,
                                        stderr=errors, timeout=180)
    text = log.read_text()
    if reject:
        require(result.returncode != 0, f'{label}: FALSE PROOF ACCEPTED')
        # Require a type-error diagnostic, not an unrelated panic/parse failure.
        # Nanoda reports failed type equality with this specific Rust assertion.
        require(result.returncode in (1, 101), f'{label}: unexpected exit {result.returncode}')
        require(any(s in text.lower() for s in (
            'type mismatch', 'definitional', 'defeq', 'not def', 'rfl', 'mismatch',
            'assertion failed: self.def_eq(u, v)')),
            f'{label}: no type-error diagnostic; inspect {log}')
    else:
        require(result.returncode == 0, f'{label}: exit {result.returncode}; inspect {log}')
    return text


def baseline():
    for filename, expected in BASELINE.items():
        require(hashlib.sha256((ROOT / filename).read_bytes()).hexdigest() == expected,
                f'{filename}: not the original reviewed input')


def artifact_source(data):
    rows = [','.join(str(n) for n in data[i:i + 16]) for i in range(0, len(data), 16)]
    return ('namespace AvgFloor\ndef artifact : List Nat :=\n  [' +
            ',\n   '.join(rows) + ']\nend AvgFloor\n')


def read_export(path):
    return [json.loads(line) for line in path.read_text().splitlines()]


def write_export(path, records):
    path.write_text(''.join(json.dumps(r, separators=(',', ':')) + '\n' for r in records))


def indexes(records):
    names = {0: ''}
    exprs = {}
    declarations = {}
    for r in records:
        if 'in' in r:
            tag = 'str' if 'str' in r else 'num'
            n = r[tag]
            leaf = n['str'] if tag == 'str' else str(n['i'])
            names[r['in']] = '.'.join(filter(None, (names[n['pre']], leaf)))
        if 'ie' in r:
            exprs[r['ie']] = r
        for kind in ('axiom', 'def', 'thm', 'opaque'):
            if kind in r:
                declarations[names[r[kind]['name']]] = (kind, r)
    return names, exprs, declarations


def audit(records, expected):
    names, _, decls = indexes(records)
    for name in expected:
        require(name in decls and decls[name][0] == 'thm', f'missing theorem {name}')
    axioms = set()
    for kind, record in decls.values():
        d = record[kind]
        if kind == 'axiom':
            name = names[d['name']]
            require(name in AXIOMS, f'unapproved axiom: {name}')
            axioms.add(name)
        if kind == 'def':
            require(d['safety'] == 'safe', 'unsafe/partial definition in proof closure')
    return sorted(axioms)


def false_type(records):
    names, exprs, _ = indexes(records)
    return next(i for i, r in exprs.items()
                if 'const' in r and names[r['const']['name']] == 'False')


def forge_false(records, theorem):
    forged = copy.deepcopy(records)
    names, _, _ = indexes(forged)
    target = next(r for r in forged if 'thm' in r and names[r['thm']['name']] == theorem)
    forged.remove(target)
    target['thm']['type'] = false_type(forged)
    forged.append(target)  # All dependencies precede their uses.
    return forged


def forge_arithmetic(records):
    forged = copy.deepcopy(records)
    names, exprs, _ = indexes(forged)
    target = next(r for r in forged if 'thm' in r and
                  names[r['thm']['name']] == 'Controls.arithmetic')
    forged.remove(target)
    old_type = exprs[target['thm']['type']]['app']  # Eq Nat 0 applied to 0.
    one = next(i for i, r in exprs.items() if r.get('natVal') == '1')
    new_type = max(exprs) + 1
    forged.append({'ie': new_type, 'app': {'fn': old_type['fn'], 'arg': one}})
    target['thm']['type'] = new_type  # Claim 0 = 1, retain Eq.refl 0 as its proof.
    forged.append(target)
    return forged


def statement_census(records):
    """Dependency closure of root TYPES, then complete referenced declarations.

    For the counts only: inductive blocks/recursor records are indivisible.
    No declaration is removed from the files sent to the kernels.
    """
    names, exprs, decls = indexes(records)
    owners = {}
    for k, r in enumerate(records):
        for kind in ('axiom', 'def', 'thm', 'opaque', 'quot', 'inductive', 'recursor'):
            if kind not in r:
                continue
            def own(obj):
                if isinstance(obj, dict):
                    if 'name' in obj:
                        owners[obj['name']] = k
                    for value in obj.values():
                        if isinstance(value, (dict, list)):
                            own(value)
                elif isinstance(obj, list):
                    for item in obj:
                        own(item)
            # Scalar declaration name or the member names in an inductive group.
            own(r[kind])
    visited_exprs, visited_records = set(), set()

    def visit_expr(i):
        if i in visited_exprs:
            return
        visited_exprs.add(i)
        r = exprs[i]
        if 'const' in r:
            name = r['const']['name']
            if name in owners:
                visit_record(owners[name])
        if 'proj' in r and r['proj']['typeName'] in owners:
            visit_record(owners[r['proj']['typeName']])
        if 'natVal' in r:
            for name, index in names.items():
                if index == 'Nat' and name in owners:
                    visit_record(owners[name])
        for tag, keys in {'app': ('fn', 'arg'), 'lam': ('type', 'body'),
                          'forallE': ('type', 'body'), 'letE': ('type', 'value', 'body'),
                          'proj': ('struct',), 'mdata': ('expr',)}.items():
            if tag in r:
                for key in keys:
                    if key in r[tag]:
                        visit_expr(r[tag][key])

    def visit_record(k):
        if k in visited_records:
            return
        visited_records.add(k)
        def walk(obj):
            if isinstance(obj, dict):
                for key, value in obj.items():
                    if key in ('type', 'value', 'rhs') and isinstance(value, int):
                        visit_expr(value)
                    elif isinstance(value, (dict, list)):
                        walk(value)
            elif isinstance(obj, list):
                for item in obj:
                    walk(item)
        walk(records[k])

    for name in ROOTS:
        visit_expr(decls[name][1]['thm']['type'])
    dependencies = sorted(name for name, owner in owners.items() if owner in visited_records)
    (OUT / 'statement-dependencies.txt').write_text(
        '\n'.join(names[name] for name in sorted(dependencies, key=lambda n: names[n])) + '\n')
    return {'statement_dependency_records': len(visited_records),
            'statement_dependency_constants': len(dependencies),
            'statement_dependency_expression_nodes': len(visited_exprs)}


def main():
    os.chdir(ROOT)
    baseline()
    if OUT.exists():
        shutil.rmtree(OUT)
    MODULES.mkdir(parents=True)
    lean = Path(shutil.which('lean') or '').resolve()
    require(lean.is_file(), 'lean is missing')
    bindir = lean.parent
    binaries = {n: bindir / n for n in ('leanexport', 'leanchecker', 'nanoda_bin', 'con-ron')}
    for n, path in binaries.items():
        require(path.is_file(), f'required independent checking tool missing: {n}')
    version = run('version', [str(lean), '--version'])
    require('version 4.35.0,' in version, 'Lean 4.35.0 is required')
    (OUT / 'toolchain.json').write_text(json.dumps({
        'lean_version': version.strip(),
        'binaries': {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                     for p in (lean, *binaries.values())},
    }, indent=2) + '\n')
    run('rebuild', ['clang', '--target=wasm32', '-O2', '-nostdlib', '-Wl,--no-entry',
                    '-Wl,--strip-all', '-Wl,--export=avg_floor', '-o',
                    str(OUT / 'rebuilt.wasm'), 'avg_floor.c'])
    data = (ROOT / 'avg_floor.wasm').read_bytes()
    require(data == (OUT / 'rebuilt.wasm').read_bytes(), 'rebuild differs from shipped module')
    print('Original C + README + WASM pinned; README build is byte-identical.', flush=True)
    (MODULES / 'Artifact.lean').write_text(artifact_source(data))
    env = dict(os.environ, LEAN_PATH=str(MODULES))
    for module in ('Artifact', 'Spec', 'Proof', 'Controls'):
        source = MODULES / 'Artifact.lean' if module == 'Artifact' else ROOT / 'verification' / (module + '.lean')
        run('compile-' + module, [str(lean), '-DwarningAsError=true', '-o',
                                  str(MODULES / (module + '.olean')), str(source)], env=env)
    exports = OUT / 'proofs.ndjson'
    run('export', [str(binaries['leanexport']), 'Proof', '--', *ROOTS], env=env, stdout=exports)
    records = read_export(exports)
    axioms = audit(records, ROOTS)
    print('Lean elaboration passed; proof axiom whitelist passed: ' + ', '.join(axioms), flush=True)

    def checkers(path, label, reject=False):
        config = OUT / (label + '-nanoda.json')
        config.write_text(json.dumps({
            'export_file_path': str(path), 'permitted_axioms': sorted(AXIOMS),
            'unpermitted_axiom_hard_error': True, 'nat_extension': True,
            'string_extension': True, 'pp_declars': [], 'pp_to_stdout': False,
            'print_success_message': True,
        }))
        commands = {
            'lean-kernel': [str(binaries['leanchecker']), '--from-export', str(path)],
            'nanoda': [str(binaries['nanoda_bin']), str(config)],
            'con-ron': [str(binaries['con-ron']), '--verified', '--jobs=2', str(path)],
        }
        for name, command in commands.items():
            run(label + '-' + name, command, env=env, reject=reject)
        print(f'{label}: all three kernels ' + ('REJECTED.' if reject else 'ACCEPTED.'), flush=True)

    checkers(exports, 'proofs')
    controls = OUT / 'controls.ndjson'
    controls_roots = ['Controls.' + n for n in ('truth', 'falsity_type', 'arithmetic', 'one')]
    run('export-controls', [str(binaries['leanexport']), 'Controls', '--', *controls_roots],
        env=env, stdout=controls)
    control_records = read_export(controls)
    audit(control_records, controls_roots)
    checkers(controls, 'valid-controls')
    attacks = {
        'false-from-true': forge_false(control_records, 'Controls.truth'),
        'zero-equals-one': forge_arithmetic(control_records),
        'false-from-real-proof': forge_false(records, 'AvgFloor.not_R1'),
    }
    for label, forged in attacks.items():
        path = OUT / (label + '.ndjson')
        write_export(path, forged)
        checkers(path, label, reject=True)
    for forbidden in ('sorryAx', 'Lean.trustCompiler', 'assumeFalse'):
        forged = copy.deepcopy(control_records)
        names, _, _ = indexes(forged)
        n = max(names) + 1
        # A fresh, well-formed axiom of False. The policy rejects even unused axioms.
        prefix, _, leaf = forbidden.rpartition('.')
        if prefix:
            forged.append({'in': n, 'str': {'pre': 0, 'str': prefix}})
            forged.append({'in': n + 1, 'str': {'pre': n, 'str': leaf}})
            n += 1
        else:
            forged.append({'in': n, 'str': {'pre': 0, 'str': leaf}})
        forged.append({'axiom': {'name': n, 'levelParams': [],
                                'type': false_type(forged), 'isUnsafe': False}})
        try:
            audit(forged, controls_roots)
        except RuntimeError as error:
            require(str(error).startswith('unapproved axiom:'), 'unexpected policy failure')
        else:
            raise RuntimeError('axiom policy accepted ' + forbidden)
    print('Axiom controls: sorryAx, Lean.trustCompiler, assumeFalse REJECTED.', flush=True)
    bad_source = OUT / 'FalseArithmetic.lean'
    bad_source.write_text('theorem falseArithmetic : (0 : Nat) = 1 := by rfl\n')
    run('frontend-false-arithmetic', [str(lean), str(bad_source)], reject=True, env=env)
    for label, offset, value in (('instruction', 59, 107), ('export-index', 49, 1)):
        bad_dir = OUT / ('mutation-' + label)
        bad_dir.mkdir()
        bad_data = bytearray(data)
        bad_data[offset] = value
        (bad_dir / 'Artifact.lean').write_text(artifact_source(bad_data))
        bad_env = dict(env, LEAN_PATH=str(bad_dir))
        for module in ('Artifact', 'Spec'):
            source = bad_dir / 'Artifact.lean' if module == 'Artifact' else ROOT / 'verification/Spec.lean'
            run('mutation-' + label + '-' + module,
                [str(lean), '-o', str(bad_dir / (module + '.olean')), str(source)], env=bad_env)
        run('mutation-' + label + '-proof',
            [str(lean), str(ROOT / 'verification/Proof.lean')], reject=True, env=bad_env)
    print('Frontend false proof and artifact instruction/export mutations REJECTED.', flush=True)
    runtime = run('runtime', ['node', 'verification/runtime.cjs'])
    print(runtime.strip(), flush=True)
    census = statement_census(records)
    for name in ('Spec', 'Proof'):
        source = (ROOT / 'verification' / (name + '.lean')).read_bytes()
        census[name + '_lines'] = len(source.splitlines())
        census[name + '_bytes'] = len(source)
    source = (MODULES / 'Artifact.lean').read_bytes()
    census['Artifact_lines'] = len(source.splitlines())
    census['Artifact_bytes'] = len(source)
    statements = '\n\n'.join(re.findall(
        r'^theorem\b.*?(?= := by)',
        (ROOT / 'verification/Proof.lean').read_text(), re.M | re.S)) + '\n'
    (OUT / 'review-statements.txt').write_text(statements)
    census['theorem_statement_lines'] = len(statements.splitlines())
    census['theorem_statement_bytes'] = len(statements.encode())
    census['export_bytes'] = exports.stat().st_size
    census['export_records'] = len(records)
    census['axioms'] = axioms
    (OUT / 'sizes.json').write_text(json.dumps(census, indent=2) + '\n')
    baseline()
    print('Review/dependency sizes: ' + json.dumps(census, sort_keys=True), flush=True)
    print('PASS: artifact-linked characterization and R1/R2 refutations; replay and controls passed.', flush=True)


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, OSError, subprocess.TimeoutExpired) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
