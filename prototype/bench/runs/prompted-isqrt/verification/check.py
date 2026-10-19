#!/usr/bin/env python3
"""Offline, fail-closed proof build, replay, and adversarial controls."""
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys

from generate import generate

ROOT = Path(__file__).resolve().parent.parent
BUILD = ROOT / '.verification-build'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def run(args, label, *, expect_failure=False, output=None, env=None):
    args = [str(x) for x in args]
    with (BUILD / 'commands.log').open('a') as log:
        log.write(shlex.join(args) + '\n')
    result = subprocess.run(args, cwd=ROOT, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (BUILD / (label + '.log')).write_text(result.stdout)
    if output is not None:
        output.write_text(result.stdout)
    if (result.returncode != 0) != expect_failure:
        print(result.stdout[-8000:], file=sys.stderr)
        raise RuntimeError(f'{label}: unexpected exit status {result.returncode}')
    return result.stdout


def tool(name, prefix):
    found = shutil.which(name)
    candidate = prefix / 'bin' / name
    if found:
        return Path(found)
    if candidate.is_file():
        return candidate
    raise RuntimeError(f'Required offline checker not installed: {name}')


def read_export(path):
    return [json.loads(line) for line in path.read_text().splitlines()]


def names_of(records):
    names = {0: ''}
    for rec in records:
        if 'in' not in rec:
            continue
        if 'str' in rec:
            part = rec['str']
            suffix = part['str']
        else:
            part = rec['num']
            suffix = str(part['i'])
        pre = names[part['pre']]
        names[rec['in']] = pre + ('.' if pre else '') + suffix
    return names


def audit(records):
    names = names_of(records)
    axioms = {names[r['axiom']['name']] for r in records if 'axiom' in r}
    if not axioms <= ALLOWED_AXIOMS:
        raise RuntimeError(f'Unapproved axioms: {sorted(axioms - ALLOWED_AXIOMS)}')
    return sorted(axioms)


def write_export(path, records):
    path.write_text(''.join(json.dumps(r, separators=(',', ':'))+'\n' for r in records))


def corrupt_controls(records, path, kind):
    # Keep every declaration well formed; change only the target theorem's type.
    rows = json.loads(json.dumps(records))
    names = names_of(rows)
    max_expr = max(r['ie'] for r in rows if 'ie' in r)
    if kind == 'false':
        false_name = next(k for k, v in names.items() if v == 'False')
        new_expr = {'ie': max_expr+1, 'const': {'name': false_name, 'us': []}}
        target = 'positiveControl'
    elif kind == 'arithmetic':
        three = next(r['ie'] for r in rows if r.get('natVal') == '3')
        target = 'arithmeticControl'
        thm = next(r['thm'] for r in rows if 'thm' in r and names[r['thm']['name']] == target)
        old_type = next(r for r in rows if r.get('ie') == thm['type'])
        new_expr = {'ie': max_expr+1, 'app': {'fn': old_type['app']['fn'], 'arg': three}}
    else:
        raise ValueError(kind)
    expr_value = {k: v for k, v in new_expr.items() if k != 'ie'}
    existing = next((r['ie'] for r in rows if 'ie' in r and
                     {k: v for k, v in r.items() if k != 'ie'} == expr_value), None)
    type_id = existing if existing is not None else max_expr+1
    # Append after all existing expressions to preserve sequential expression IDs.
    for i, rec in enumerate(rows):
        if 'thm' in rec and names[rec['thm']['name']] == target:
            thm_record = rows.pop(i)
            thm_record['thm']['type'] = type_id
            if existing is None:
                rows.append(new_expr)
            rows.append(thm_record)
            break
    write_export(path, rows)


def main():
    os.chdir(ROOT)
    if BUILD.exists():
        shutil.rmtree(BUILD)
    BUILD.mkdir()
    lean = shutil.which('lean')
    if not lean:
        raise RuntimeError('Lean 4.35.0 is required')
    prefix = Path(subprocess.check_output([lean, '--print-prefix'], text=True).strip())
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    if 'version 4.35.0,' not in version:
        raise RuntimeError(f'Expected Lean 4.35.0, got {version}')
    export = tool('leanexport', prefix)
    default = tool('leanchecker', prefix)
    nanoda = tool('nanoda_bin', prefix)
    conron = tool('con-ron', prefix)
    env = dict(os.environ, LEAN_PATH=str(BUILD))
    original = {p: (ROOT / p).read_bytes() for p in ['isqrt.c', 'isqrt.wasm', 'README.md']}
    print('[1/6] Rebuild unchanged C; compare every Wasm byte', flush=True)
    run(['clang', '--target=wasm32', '-O2', '-nostdlib', '-Wl,--no-entry',
         '-Wl,--strip-all', '-Wl,--export=isqrt', '-o', BUILD / 'rebuilt.wasm',
         'isqrt.c'], 'rebuild')
    if (BUILD / 'rebuilt.wasm').read_bytes() != original['isqrt.wasm']:
        raise RuntimeError('C rebuild differs from shipped isqrt.wasm')
    generate(ROOT / 'isqrt.wasm', BUILD)

    def compile_module(name, *, source=None, fail=False, label=None, target=None):
        source = source or ROOT / 'verification' / f'{name}.lean'
        run([lean, '-R', source.parent, '-o', target or BUILD / f'{name}.olean', source],
            label or name, expect_failure=fail, env=env)

    print('[2/6] Compile Lean proofs against freshly read artifact bytes', flush=True)
    for name in ['Semantics', 'Artifact', 'Bytecode', 'Machine', 'Chunks', 'Trace',
                 'Correctness', 'Requirements', 'Controls']:
        src = BUILD / f'{name}.lean' if name in ['Artifact', 'Bytecode'] else None
        compile_module(name, source=src)
    proof_export = BUILD / 'requirements.ndjson'
    run([export, 'Requirements', '--', 'requirements'], 'export', output=proof_export, env=env)
    records = read_export(proof_export)
    axioms = audit(records)
    names = names_of(records)
    roots = [r['thm'] for r in records if 'thm' in r and names[r['thm']['name']] == 'requirements']
    if len(roots) != 1:
        raise RuntimeError('Export must contain exactly one requirements theorem')

    def replays(path, label, fail=False):
        audit(read_export(path))
        cfg = BUILD / (label + '.nanoda.json')
        cfg.write_text(json.dumps({
            'export_file_path': str(path), 'permitted_axioms': sorted(ALLOWED_AXIOMS),
            'unpermitted_axiom_hard_error': True, 'nat_extension': True,
            'string_extension': True, 'pp_declars': [], 'pp_to_stdout': False,
            'print_success_message': True}))
        commands = [
            ('lean', [default, '--from-export', path]),
            ('nanoda', [nanoda, cfg]),
            ('con-ron', [conron, '--verified', '--jobs=2', path])]
        for checker, args in commands:
            text = run(args, label+'-'+checker, expect_failure=fail, env=env)
            if fail:
                # Rejecting syntax, missing files, or missing tools is not a proof test.
                if checker == 'lean' and 'kernel rejects the solution' not in text:
                    raise RuntimeError('Default kernel did not reach proof rejection')
                if checker == 'nanoda' and not ('src/tc.rs' in text and 'def_eq' in text):
                    raise RuntimeError('Nanoda did not report a type-checking rejection')
                if checker == 'con-ron' and not any(x in text.lower() for x in ['reject', 'mismatch', 'type']):
                    raise RuntimeError('con-ron did not report proof rejection')
            print(f'  {checker}: {"rejected false proof" if fail else "accepted"}', flush=True)

    print('[3/6] Replay full transitive proof dependency closure in three kernels', flush=True)
    replays(proof_export, 'requirements')
    print('[4/6] Positive and deliberately false proof controls, same replay path', flush=True)
    controls = BUILD / 'controls.ndjson'
    run([export, 'Controls', '--', 'positiveControl', 'arithmeticControl', 'controlThree', 'False'],
        'export-controls', output=controls, env=env)
    replays(controls, 'positive')
    for kind in ['false', 'arithmetic']:
        path = BUILD / f'negative-{kind}.ndjson'
        corrupt_controls(read_export(controls), path, kind)
        replays(path, 'negative-'+kind, fail=True)

    print('[5/6] Reject sorry/unapproved axioms and a changed artifact', flush=True)
    sorry_source = BUILD / 'SorryControl.lean'
    sorry_source.write_text('theorem sorryControl : False := by sorry\n')
    compile_module('SorryControl', source=sorry_source)
    sorry_export = BUILD / 'sorry.ndjson'
    run([export, 'SorryControl', '--', 'sorryControl'], 'export-sorry', output=sorry_export, env=env)
    try:
        audit(read_export(sorry_export))
    except RuntimeError as e:
        if 'sorryAx' not in str(e):
            raise
    else:
        raise RuntimeError('Axiom audit accepted sorryAx')
    # Mutate the initial i32.const 65536 to 49152, preserving encoding length.
    # Recompile the *same* initialization theorem against the new bytes/facts.
    mutant = BUILD / 'mutant'
    mutant.mkdir()
    changed = bytearray(original['isqrt.wasm'])
    if changed[67:71] != bytes([0x41,0x80,0x80,0x04]):
        raise RuntimeError('Mutation-control offset no longer matches the artifact')
    changed[70] = 3
    (mutant / 'isqrt.wasm').write_bytes(changed)
    generate(mutant / 'isqrt.wasm', mutant)
    mutant_env = dict(env, LEAN_PATH=str(mutant)+os.pathsep+str(BUILD))
    for name in ['Artifact', 'Bytecode']:
        run([lean, '-R', mutant, '-o', mutant / f'{name}.olean', mutant / f'{name}.lean'],
            'mutant-'+name, env=mutant_env)
    rejected = run([lean, '-R', ROOT / 'verification', '-o', mutant / 'Machine.olean',
                   ROOT / 'verification' / 'Machine.lean'], 'mutant-Machine',
                  expect_failure=True, env=mutant_env)
    if 'initialize_state' not in rejected and 'unsolved goals' not in rejected and 'Tactic' not in rejected:
        raise RuntimeError('Artifact mutation did not reach a proof failure')
    print('  sorryAx rejected; changed bytes fail initialization proof', flush=True)

    print('[6/6] Report review surface and verify inputs stayed unchanged', flush=True)
    for p, before in original.items():
        if (ROOT / p).read_bytes() != before:
            raise RuntimeError(f'Input changed during verification: {p}')
    spec = (ROOT / 'verification' / 'Semantics.lean').read_text()
    req = (ROOT / 'verification' / 'Requirements.lean').read_text().split(' := by', 1)[0]
    artifact = (BUILD / 'Artifact.lean').read_text()
    review = spec + '\n' + artifact + '\n' + req + '\n'
    (BUILD / 'REVIEW.txt').write_text(review)
    report = {
        'lean': version, 'axioms': axioms,
        'sha256': {p: hashlib.sha256(b).hexdigest() for p, b in original.items()},
        'review_lines': len(review.splitlines()), 'review_bytes': len(review.encode()),
        'export_bytes': proof_export.stat().st_size,
        'export_declaration_records': sum(any(k in r for k in
            ['def','opaque','thm','axiom','inductive','quot']) for r in records),
        'export_kernel_constants': sum(
            sum(len(r['inductive'][k]) for k in ['types','ctors','recs']) if 'inductive' in r
            else int(any(k in r for k in ['def','opaque','thm','axiom','quot'])) for r in records),
        'replay_tools': {str(p.resolve()): hashlib.sha256(p.read_bytes()).hexdigest()
                         for p in [default, nanoda, conron, export]},
        'kernels': ['Lean C++ (leanchecker --from-export)', 'Nanoda Rust', 'con-ron Rust --verified'],
        'controls': ['positive proof', 'False with True.intro', '1+1=3 with proof of 1+1=2',
                     'sorryAx axiom audit', 'artifact constant mutation'],
    }
    (BUILD / 'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(f'PASS: R1 and R2; three kernels; all negative controls rejected.', flush=True)
    print(f'Review surface: {report["review_lines"]} lines, {report["review_bytes"]} UTF-8 bytes.')
    print('Details: .verification-build/report.json and commands.log')


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, subprocess.SubprocessError, OSError, ValueError, KeyError, StopIteration) as e:
        sys.exit(f'FAIL: {e}')
