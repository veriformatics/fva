#!/usr/bin/env python3
"""Offline reproduction: exact binary, two runtimes, closed proof replays, canaries."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
os.chdir(ROOT)
OUT = ROOT / '.verification'
OUT.mkdir(exist_ok=True)
ENV = dict(os.environ, XDG_CACHE_HOME=str(OUT / 'cache'))
BIN = Path(shutil.which('lean')).resolve().parent


def run(args, *, reject=False, output=None, diagnostic=None, code=None):
    p = subprocess.run([str(a) for a in args], env=ENV, capture_output=True, text=True)
    if output:
        Path(output).write_text(p.stdout)
    log = p.stdout + p.stderr
    if reject:
        assert p.returncode != 0, f'FALSE CLAIM ACCEPTED: {args}'
        if code is not None:
            assert p.returncode == code, log
        assert diagnostic and diagnostic in log, f'Not the expected rejection: {log}'
        print(f'REJECTED as required: {args[0]} ({diagnostic})', flush=True)
    else:
        assert p.returncode == 0, f'{args}:\n{log}'
        if not output:
            print(log.strip() or f'OK: {args[0]}', flush=True)
    return p


artifact = Path('lz4-block-codec.wasm').read_bytes()
assert len(artifact) == 1226
assert hashlib.sha256(artifact).hexdigest() == \
    '4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf'
assert artifact[0x32a:0x32f] == bytes([0x20, 3, 0x2d, 0, 0])  # local.get 3; load8_u
run(['wasm-tools', 'validate', 'lz4-block-codec.wasm'])
run(['wasm-tools', 'dump', 'lz4-block-codec.wasm'], output=OUT / 'artifact.dump')
print('Exact README artifact: 1226 bytes, SHA-256 matched', flush=True)

# Rebuild the target from source even if Lake has cached an earlier proof.
source = Path('Proofs/Counterexamples.lean')
run(['lake', 'env', 'lean', source, '-o', OUT / 'Counterexamples.olean'])
run(['lake', 'build'])
witness = {}
for name in ['encoderInput', 'encoderBlock', 'decoderBlock', 'decoderContent']:
    match = re.search(rf'def {name} : List Nat := (\[[0-9,]+\])', source.read_text())
    assert match, name
    witness[name] = json.loads(match[1])
(OUT / 'witnesses.json').write_text(json.dumps(witness))

# WAST imports the original module, embedded byte for byte, rather than WAT source.
escape = lambda bs: ''.join(f'\\{b:02x}' for b in bs)
wast = f'(module $codec binary "{escape(artifact)}")\n(register "codec" $codec)\n'
wast += f'''(module $test
  (import "codec" "memory" (memory 1))
  (import "codec" "lz4BlockEncode" (func $enc (param i32 i32 i32) (result i32)))
  (import "codec" "lz4BlockDecode" (func $dec (param i32 i32 i32) (result i32)))
  (data (i32.const 4096) "{escape(witness['decoderBlock'])}")
  (data (i32.const 60000) "{escape(witness['encoderInput'])}")
  (data (i32.const 65535) "\\00")
  (func (export "r2") (result i32) i32.const 4096 i32.const 10 i32.const 1024 call $dec)
  (func (export "r2control") (result i32) i32.const 4096 i32.const 10 i32.const 8192 call $dec)
  (func (export "r3") (result i32) i32.const 65535 i32.const 1 i32.const 1024 call $dec)
  (func (export "grow") (result i32) i32.const 5 memory.grow)
  (func (export "init") (local $p i32)
    (loop $next local.get $p i32.const -65536 i32.store
      local.get $p i32.const 4 i32.add local.tee $p i32.const 262144 i32.lt_u br_if $next))
  (func (export "byte") (param i32) (result i32) local.get 0 i32.load8_u)
  (func (export "input") i32.const 262144 i32.const 60000 i32.const 13 memory.copy)
  (func (export "enc") (result i32) i32.const 262144 i32.const 13 i32.const 327680 call $enc)
  (func (export "roundtrip") (result i32) i32.const 327680 i32.const 13 i32.const 350000 call $dec)
)
(assert_return (invoke $test "r2") (i32.const 1))
(assert_return (invoke $test "r2control") (i32.const 13))
(assert_trap (invoke $test "r3") "out of bounds memory access")
'''


def check_bytes(address, values):
    return ''.join(f'(assert_return (invoke $test "byte" (i32.const {address+i})) '
                   f'(i32.const {b}))\n' for i, b in enumerate(values))


wast += check_bytes(1024, [97] + [0] * 12)
wast += check_bytes(8192, witness['decoderContent'])
wast += '''(assert_return (invoke $test "grow") (i32.const 1))
(invoke $test "input")
(invoke $test "init")
(assert_return (invoke $test "enc") (i32.const 13))
'''
wast += check_bytes(327680, witness['encoderBlock'])
wast += '(assert_return (invoke $test "roundtrip") (i32.const 13))\n'
wast += check_bytes(350000, witness['encoderInput'])
(OUT / 'runtime.wast').write_text(wast)
run(['wasmtime', 'wast', OUT / 'runtime.wast'])
print('Wasmtime: all counterexample observations reproduced', flush=True)
bad_wast = wast.replace('(invoke $test "r2") (i32.const 1)',
                        '(invoke $test "r2") (i32.const 13)')
assert bad_wast != wast
(OUT / 'false-runtime.wast').write_text(bad_wast)
run(['wasmtime', 'wast', OUT / 'false-runtime.wast'], reject=True,
    diagnostic="result 0 didn't match", code=1)
run(['node', 'verification/runtime.cjs'])

# Export only the named proofs and their transitive dependencies.
names = ['Counterexamples.' + n for n in
         ['r1', 'r2', 'r3', 'kernelCanary', 'falseIdentity']]
export = OUT / 'proofs.ndjson'
run(['lake', 'env', BIN / 'leanexport', 'Proofs.Counterexamples', '--', *names],
    output=export)
records = [json.loads(line) for line in export.read_text().splitlines()]
name_map = {0: ''}
for record in records:
    if 'in' in record:
        part = record.get('str', record.get('num'))
        parent = name_map[part['pre']]
        name_map[record['in']] = (parent + '.' if parent else '') + str(part.get('str', part.get('i')))
assert not any('axiom' in r for r in records), 'Expected an axiom-free closure'
theorems = {name_map[r['thm']['name']] for r in records if 'thm' in r}
assert set(names) <= theorems
false_expr = next(r['ie'] for r in records
                  if 'const' in r and name_map[r['const']['name']] == 'False')
mutated = json.loads(json.dumps(records))
for r in mutated:
    if 'thm' in r and name_map[r['thm']['name']] == 'Counterexamples.kernelCanary':
        r['thm']['type'] = false_expr  # True.intro : False (well-formed, ill-typed).
false_export = OUT / 'false-proof.ndjson'
false_export.write_text(''.join(json.dumps(r) + '\n' for r in mutated))
for checker in ['con-ron', 'con-leche']:
    run([BIN / checker, '--verified', '--jobs=2', export])
    run([BIN / checker, '--verified', '--jobs=2', false_export], reject=True,
        diagnostic='type mismatch in theorem', code=1)
for path, bad in [(export, False), (false_export, True)]:
    config = OUT / ('nanoda-false.json' if bad else 'nanoda.json')
    config.write_text(json.dumps({'export_file_path': str(path), 'permitted_axioms': [],
                                 'unpermitted_axiom_hard_error': True,
                                 'nat_extension': True, 'string_extension': True}))
    run([BIN / 'nanoda_bin', config], reject=bad,
        diagnostic='assertion failed: self.def_eq(u, v)' if bad else None,
        code=101 if bad else None)

for name, claim in [('false', 'False := True.intro'), ('unequal', '(0 : Nat) = 1 := rfl')]:
    negative = OUT / f'{name}.lean'
    negative.write_text('import Init\ntheorem bad : ' + claim + '\n')
    run(['lake', 'env', 'lean', negative], reject=True, diagnostic='error:', code=1)

files = ['Proofs.lean', 'Proofs/Counterexamples.lean', 'check.py', 'verification/runtime.cjs']
sizes = {f: {'lines': len(Path(f).read_text().splitlines()), 'bytes': Path(f).stat().st_size}
         for f in files}
census = {k: sum(k in r for r in records) for k in
          ['def', 'thm', 'inductive', 'opaque', 'axiom', 'quot']}
report = {'review_files': sizes, 'full_export_bytes': export.stat().st_size,
          'full_export_records': len(records), 'declaration_records': census}
(OUT / 'sizes.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2), flush=True)
print('SUCCESS: R1, R2, R3 refuted; both runtimes agree; three independent kernel replays pass; all negative controls rejected.', flush=True)
