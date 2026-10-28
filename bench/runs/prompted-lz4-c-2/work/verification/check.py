"""One offline command: rebuild, replay, negative controls, runtime comparison."""
import json
import hashlib
import shutil
from pathlib import Path
import subprocess
import sys
from runtime import make_wast

if not __debug__:
    raise RuntimeError('Run without Python assertion optimization')

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.lake' / 'verification'
OUT.mkdir(parents=True, exist_ok=True)
BIN = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip()) / 'bin'
AXIOMS = ['propext', 'Classical.choice', 'Quot.sound']
THEOREMS = ['Prefix.decoder_is_artifact', 'Prefix.zero_capacity', 'Prefix.zero_input',
            'Results.checked_cases', 'Results.successful_cases_parse', 'Results.strict_case_count']


def run(name, args, *, reject=False, needle=None, stdout_file=None):
    p = subprocess.run(args, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=600)
    (OUT / (name + '.log')).write_bytes(p.stdout + p.stderr)
    if stdout_file:
        stdout_file.write_bytes(p.stdout)
    if (p.returncode == 0) == reject:
        raise RuntimeError(f'{name}: unexpected exit {p.returncode}; see {OUT / (name + ".log")}')
    if needle and needle.encode() not in p.stdout + p.stderr:
        raise RuntimeError(f'{name}: missing diagnostic {needle!r}')
    print(name + ': OK' + (' (rejected)' if reject else ''), flush=True)
    return p.stdout


def nanoda(name, export, *, reject=False, needle=None, declarations=None):
    config = {'export_file_path': str(export), 'permitted_axioms': AXIOMS,
              'unpermitted_axiom_hard_error': True, 'nat_extension': True,
              'string_extension': True, 'print_success_message': True,
              'pp_declars': declarations or [], 'pp_to_stdout': bool(declarations)}
    config_path = OUT / (name + '.json')
    config_path.write_text(json.dumps(config, indent=2) + '\n')
    return run(name, [str(BIN / 'nanoda_bin'), str(config_path)], reject=reject, needle=needle)


run('artifact', [sys.executable, 'verification/extract.py', '--check'])
run('wasm-validation', ['wasm-tools', 'validate', 'lz4-c.wasm'])
run('clean', ['lake', 'clean', 'proofs'])
run('build', ['lake', 'build'])
run('cpp-kernel', ['lake', 'env', str(BIN / 'leanchecker-paranoid'), 'Proofs'])
proof_export = OUT / 'proofs.ndjson'
run('export', ['lake', 'env', str(BIN / 'leanexport'), 'Proofs', '--'] + THEOREMS,
    stdout_file=proof_export)
replay = nanoda('independent-rust-kernel', proof_export, declarations=THEOREMS)
for theorem in THEOREMS:
    assert ('theorem ' + theorem + ' ').encode() in replay, f'missing checked theorem {theorem}'
assert b'with no errors' in replay

# Source-level failure, followed by forged .olean failures; checking only a
# malformed Lean source would not exercise the replay kernels.
source = OUT / 'FalseSource.lean'
source.write_text('theorem impossible : False := by exact True.intro\n')
run('source-negative', ['lake', 'env', 'lean', str(source)], reject=True, needle='Type mismatch')
negative_dir = ROOT / '.lake' / 'build' / 'lib' / 'lean' / 'verification'
negative_dir.mkdir(parents=True, exist_ok=True)
for module, theorem in [('BadProof', 'badFalse'), ('BadEquality', 'badEquality'), ('BadAxiom', 'badAxiom')]:
    run('make-' + module, ['lake', 'env', 'lean', '-o', str(negative_dir / (module + '.olean')),
                          f'verification/{module}.lean'])
    if module != 'BadAxiom':
        run('cpp-negative-' + module,
            ['lake', 'env', str(BIN / 'leanchecker-paranoid'), 'verification.' + module],
            reject=True, needle='type mismatch')
    export = OUT / (module + '.ndjson')
    run('export-' + module,
        ['lake', 'env', str(BIN / 'leanexport'), 'verification.' + module, '--', theorem],
        stdout_file=export)
    nanoda('rust-negative-' + module, export, reject=True,
           needle='sorryAx' if module == 'BadAxiom' else 'assertion failed')

case_json = run('emit-cases', ['lake', 'env', 'lean', '--run', 'verification/Emit.lean'])
cases = json.loads(case_json)
assert len(cases) == 19
for wrong in [False, True]:
    path = OUT / ('wrong.wast' if wrong else 'cases.wast')
    path.write_text(make_wast(ROOT, cases, wrong))
    run('wasmtime-negative' if wrong else 'wasmtime-cases', ['wasmtime', 'wast', '-C', 'cache=n', str(path)],
        reject=wrong, needle='expected' if wrong else None)

review = [ROOT / 'Proofs.lean', ROOT / 'check.sh']
review += sorted(p for p in (ROOT / 'Proofs').glob('*.lean') if p.name != 'Artifact.lean')
review += sorted((ROOT / 'verification').glob('*.py'))
review += sorted((ROOT / 'verification').glob('*.lean'))
print(f'Local handwritten review surface: {sum(len(p.read_bytes().splitlines()) for p in review)} lines, '
      f'{sum(p.stat().st_size for p in review)} bytes (includes proofs and test setup).')
tools = [Path(shutil.which(n)) for n in ['lean', 'lake', 'wasm-tools', 'wasmtime', 'python3']]
tools += [BIN / n for n in ['leanchecker-paranoid', 'leanexport', 'nanoda_bin']]
(OUT / 'tools.json').write_text(json.dumps({str(p): {
    'bytes': p.stat().st_size, 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
    for p in tools}, indent=2) + '\n')

print('CHECK PASSED: artifact-linked partial proofs replayed; all negative controls rejected.')
print('R1, R2, R3 remain unproved in general. Read VERIFICATION.md for the exact scope.')
