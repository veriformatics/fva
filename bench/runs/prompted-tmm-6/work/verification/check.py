"""Offline build, artifact binding, axiom audit, and independent kernel replay."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / '.verification'
OUT.mkdir(exist_ok=True)

def run(args, *, output=None, expected=0):
    print('+', ' '.join(map(str, args)), flush=True)
    result = subprocess.run(list(map(str, args)), cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if output:
        Path(output).write_text(result.stdout)
    else:
        print(result.stdout, end='', flush=True)
    if result.returncode != expected:
        if output:
            print(result.stdout[-12000:])
        raise RuntimeError(f'exit {result.returncode}, expected {expected}: {args}')
    return result.stdout

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
def audit(path, required=()):
    names = {0: ''}
    declarations = set()
    axioms = set()
    records = [json.loads(s) for s in Path(path).read_text().splitlines()]
    for record in records:
        if 'in' in record:
            part = record.get('str', record.get('num'))
            suffix = str(part.get('str', part.get('i')))
            prefix = names[part['pre']]
            names[record['in']] = prefix + ('.' if prefix else '') + suffix
        for kind in ('def', 'thm', 'opaque', 'axiom'):
            if kind in record:
                name = names[record[kind]['name']]
                declarations.add(name)
                if kind == 'axiom':
                    axioms.add(name)
    assert set(required) <= declarations, 'missing requested theorem'
    assert axioms <= ALLOWED, f'unapproved axioms: {axioms - ALLOWED}'
    print(f'Axiom audit: {sorted(axioms)}; {len(records)} export records', flush=True)
    return records, names

def main():
    for name, digest in json.loads((ROOT/'verification/original-sha256.json').read_text()).items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, f'changed original: {name}'
    run([sys.executable, 'verification/embed.py', '--check'])
    # Rebuild our modules, even if the caller has stale local oleans.
    for name in ('Proofs', 'Proofs.olean', 'Proofs.ilean', 'Proofs.olean.server', 'Proofs.olean.private'):
        target = ROOT/'.lake/build/lib/lean'/name
        if target.is_dir():
            shutil.rmtree(target)
        elif target.exists():
            target.unlink()
    run(['lake', '--no-cache', 'build'])
    run(['Rscript', 'verification/reproduce.R'])
    prefix = Path(run(['lean', '--print-prefix']).strip())/'bin'
    theorems = ['matrix_shape', 'libraries', 'reference_eq', 'pair_count', 'cutoff_inactive',
                'retained_eq', 'rawFirst_upper', 'R1_failure', 'R2_failure',
                'R3_failure', 'R3_gap']
    required = ['Verification.'+s for s in theorems]
    export = OUT/'proofs.ndjson'
    run(['lake', 'env', prefix/'leanexport', 'Proofs', '--', *required], output=export)
    audit(export, required)

    run(['lake', 'env', 'lean', '-o', '.lake/build/lib/lean/FalseControl.olean', 'FalseControl.lean'])
    good = OUT/'control-good.ndjson'
    run(['lake', 'env', prefix/'leanexport', 'FalseControl', '--',
         'VerificationControlTrue', 'VerificationControlFalseType'], output=good)
    records, names = audit(good, ['VerificationControlTrue'])
    false_name = next(n for n, s in names.items() if s == 'False')
    false_expr = next(r['ie'] for r in records if r.get('const', {}).get('name') == false_name)
    theorem = next(r for r in records if 'thm' in r)
    records.remove(theorem)
    theorem['thm']['type'] = false_expr
    records.append(theorem)  # False has been declared by this point.
    bad = OUT/'control-false.ndjson'
    bad.write_text(''.join(json.dumps(r)+'\n' for r in records))
    sorry = OUT/'control-sorry.ndjson'
    run(['lake', 'env', prefix/'leanexport', 'FalseControl', '--',
         'VerificationSorryFalse'], output=sorry)
    try:
        audit(sorry)
    except AssertionError as e:
        assert 'unapproved axioms' in str(e)
        print('Axiom audit rejects the sorry-based proof of False', flush=True)
    else:
        raise AssertionError('axiom audit accepted sorry')

    for kernel in ('leanchecker', 'lean4lean', 'nanoda_bin', 'con-ron'):
        def command(path):
            if kernel == 'nanoda_bin':
                config = OUT/(path.stem+'.nanoda.json')
                config.write_text(json.dumps(dict(export_file_path=str(path),
                    permitted_axioms=sorted(ALLOWED), unpermitted_axiom_hard_error=True,
                    nat_extension=True, string_extension=True, num_threads=4)))
                return [prefix/kernel, config]
            flag = {'leanchecker': ['--from-export'], 'lean4lean': ['--import'], 'con-ron': []}[kernel]
            return [prefix/kernel, *flag, path]
        run(command(good), output=OUT/(kernel+'-control-good.log'))
        rejection = run(command(bad), output=OUT/(kernel+'-control-false.log'),
                        expected=101 if kernel == 'nanoda_bin' else 1)
        if kernel == 'nanoda_bin':
            assert 'assertion failed: self.def_eq(u, v)' in rejection
        print(f'{kernel}: accepted valid control; rejected True.intro : False', flush=True)
        run(command(export), output=OUT/(kernel+'-proofs.log'))
        print(f'{kernel}: all verification proofs accepted', flush=True)
    print('VERIFICATION SUCCESS: artifact binding, proofs, four kernels, and negative controls passed')

if __name__ == '__main__':
    main()
