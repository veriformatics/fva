#!/usr/bin/env python3
"""Reproduce counterexamples on the unchanged binary; replay specification facts."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

if not __debug__:
    raise RuntimeError('Python assertions must be enabled')

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / '.verification'
OUT.mkdir(exist_ok=True)


def run(args, *, log, reject=False, trap=False, contains=()):
    p = subprocess.run(args, cwd=ROOT, text=True, capture_output=True, timeout=120)
    text = p.stdout + p.stderr
    (OUT / log).write_text(text)
    expected_codes = (1, 134) if trap else ((1,) if reject else (0,))
    assert p.returncode in expected_codes, (args, p.returncode, text)
    assert all(s in text for s in contains), (args, text)
    return text


# Pin the artifact and the exact requirements used by this verification.
PINS = {
    'lz4-block-codec.wasm': '4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf',
    'lz4_Block_format.md': 'dce3c34a8738c44ed1dffb48c73e30297fca98ba7881408dc228865912c9a42e',
    'README.md': '84232202637378126a384cc564d46f09b3ce750aa580c37ee91a4661a0417814',
    'lz4-block-codec.wat': '737b63992149810690086420d4802d86db058359c998768a9737962c974250e3',
    'CHECK.md': 'aba7a0ca513f6b4473abff323da5dd4ddcf9cd021c015ee4fcb9138fc0d0d44e',
}
for name, digest in PINS.items():
    assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, name
binary = (ROOT / 'lz4-block-codec.wasm').read_bytes()
assert len(binary) == 1226
c = json.loads((ROOT / 'verification/cases.json').read_text())


# Specification parser: natural lengths, bytewise forward (overlapping) matches.
# End rules are checked separately, so the malformed encoder output can be parsed.
def parse(block):
    p, out, literal_counts, matches = 0, bytearray(), [], []
    ended_with_literals = False

    def length(base):
        nonlocal p
        n = base
        if base == 15:
            while True:
                assert p < len(block)
                b = block[p]
                p += 1
                n += b
                if b != 255:
                    break
        return n

    while p < len(block):
        token = block[p]
        p += 1
        n = length(token >> 4)
        literal_counts.append(n)
        assert p + n <= len(block)
        out.extend(block[p:p+n])
        p += n
        if p == len(block):
            ended_with_literals = True
            break
        assert p + 2 <= len(block)
        offset = int.from_bytes(block[p:p+2], 'little')
        p += 2
        assert 0 < offset <= len(out)
        n = 4 + length(token & 15)
        matches.append((len(out), offset, n))
        for _ in range(n):
            out.append(out[-offset])
    assert block and p == len(block) and ended_with_literals
    last = literal_counts[-1]
    tail_ok = last >= 5 or (len(out) < 5 and len(literal_counts) == 1 and last == len(out))
    match_ok = not matches or len(out) - matches[-1][0] >= 12
    return bytes(out), literal_counts, matches, tail_ok, match_ok


assert parse(bytes.fromhex(c['encodedHex'])) == (
    c['encodeInput'].encode(), [5, 4], [(5, 5, 4)], False, False)
assert parse(bytes.fromhex(c['validHex'])) == (
    c['decodedText'].encode(), [1, 5], [(1, 1, 7)], True, True)
assert parse(b'\0') == (b'', [0], [], True, True)
print('Format: R1 violates both end rules; R2 and empty blocks are valid', flush=True)


# WAST imports the exact binary, without translating or instrumenting it.
def wast(cases):
    escaped = lambda b: ''.join(f'\\{v:02x}' for v in b)
    input_bytes = cases['encodeInput'].encode()
    expected = bytes.fromhex(cases['encodedHex'])
    valid = bytes.fromhex(cases['validHex'])
    decoded = cases['decodedText'].encode()
    stores = '\n'.join(f'(i32.store8 (i32.const {262144+i}) (i32.const {v}))'
                       for i, v in enumerate(input_bytes))
    s = f'''(module $codec binary "{escaped(binary)}")
(register "codec" $codec)
(module $test
 (import "codec" "memory" (memory 1))
 (import "codec" "lz4BlockEncode" (func $enc (param i32 i32 i32) (result i32)))
 (import "codec" "lz4BlockDecode" (func $dec (param i32 i32 i32) (result i32)))
 (data (i32.const 1024) "{escaped(valid)}")
 (func (export "read") (param i32) (result i32) (i32.load8_u (local.get 0)))
 (func (export "low") (result i32) (call $dec (i32.const 1024) (i32.const {len(valid)}) (i32.const 0)))
 (func (export "high") (result i32) (call $dec (i32.const 1024) (i32.const {len(valid)}) (i32.const 2048)))
 (func (export "padded") (param i32) (result i32)
  (i32.store8 (i32.const 1024) (i32.const 0))
  (i32.store8 (i32.const 1025) (local.get 0))
  (i32.store8 (i32.const 1026) (i32.const 0))
  (i32.store8 (i32.const 2047) (i32.const 65))
  (i32.store (i32.const 2048) (i32.const 0))
  (call $dec (i32.const 1024) (i32.const 1) (i32.const 2048)))
 (func (export "empty") (result i32) (call $dec (i32.const 65535) (i32.const 1) (i32.const 0)))
 (func (export "encode") (result i32) (local $p i32)
  (drop (memory.grow (i32.const 5)))
  (loop $init
   (i32.store (local.get $p) (i32.const -65536))
   (local.set $p (i32.add (local.get $p) (i32.const 4)))
   (br_if $init (i32.lt_u (local.get $p) (i32.const 262144))))
  {stores}
  (call $enc (i32.const 262144) (i32.const {len(input_bytes)}) (i32.const 300000))))
(assert_return (invoke $codec "getLinearMemoryOffset") (i32.const 0))
(assert_return (invoke $test "low") (i32.const 1))
(assert_return (invoke $test "read" (i32.const 0)) (i32.const 65))
(assert_return (invoke $test "high") (i32.const {len(decoded)}))
'''
    for i, v in enumerate(decoded):
        s += f'(assert_return (invoke $test "read" (i32.const {2048+i})) (i32.const {v}))\n'
    s += f'''(assert_return (invoke $test "padded" (i32.const 0)) (i32.const 0))
(assert_return (invoke $test "padded" (i32.const 1)) (i32.const 4))
(assert_trap (invoke $test "empty") "out of bounds memory access")
(assert_return (invoke $test "encode") (i32.const {len(expected)}))
'''
    for address, data in [(262144, input_bytes), (300000, expected)]:
        for i, v in enumerate(data):
            s += f'(assert_return (invoke $test "read" (i32.const {address+i})) (i32.const {v}))\n'
    return s


wasmtime = shutil.which('wasmtime')
assert wasmtime
run(['wasm-tools', 'validate', 'lz4-block-codec.wasm'], log='wasm-validation.log')
run(['wasm-tools', 'dump', 'lz4-block-codec.wasm'], log='artifact.dump')
# A direct call on the unwrapped artifact identifies the failing instruction as a load.
assert binary[0x32c:0x32f] == b'\x2d\x00\x00'  # i32.load8_u, offset 0
run([wasmtime, '-C', 'cache=n', '--invoke', 'lz4BlockDecode',
     'lz4-block-codec.wasm', '65535', '1', '0'], log='direct-trap.log', trap=True,
    contains=('0x32c', 'wasm address 0x10000', 'out of bounds memory access'))
(OUT / 'witnesses.wast').write_text(wast(c))
run([wasmtime, 'wast', '-C', 'cache=n', str(OUT / 'witnesses.wast')], log='wasmtime.log')
run(['node', 'verification/runtime.js', 'verification/cases.json'], log='v8.log')
print('Wasmtime + V8: all three counterexamples reproduced on pinned binary', flush=True)
# Negative execution controls: demand an incorrect final byte from the real encoder.
bad = dict(c, encodedHex=c['encodedHex'][:-2] + '00')
(OUT / 'bad-cases.json').write_text(json.dumps(bad))
(OUT / 'bad.wast').write_text(wast(bad))
run([wasmtime, 'wast', '-C', 'cache=n', str(OUT / 'bad.wast')],
    log='wasmtime-negative.log', reject=True, contains=('expected',))
run(['node', 'verification/runtime.js', str(OUT / 'bad-cases.json')],
    log='v8-negative.log', reject=True, contains=('AssertionError',))
print('Both execution checkers reject the false encoder-output assertion', flush=True)


# Export only the complete dependency closure of these six proved statements.
roots = ['r1_bad_tail', 'r1_bad_match', 'r2_end_rules',
         'empty_literal_block', 'empty_tail', 'kernel_control']
run(['lake', 'build'], log='build.log')
lean_bin = Path(run(['lean', '--print-prefix'], log='lean-prefix.log').strip()) / 'bin'
export = run(['lake', 'env', str(lean_bin / 'leanexport'), 'Proofs.FormatFacts', '--']
             + ['FormatFacts.' + n for n in roots], log='proofs.ndjson')
records = [json.loads(line) for line in export.splitlines()]
assert not any('axiom' in r for r in records), 'Proofs must be axiom-free'
names = {0: ''}
for r in records:
    if 'in' in r:
        v = r.get('str', r.get('num'))
        names[r['in']] = (names[v['pre']] + '.' + str(v.get('str', v.get('i')))).strip('.')
assert all(any('thm' in r and names[r['thm']['name']] == 'FormatFacts.' + n
               for r in records) for n in roots)
checkers = [
    [str(lean_bin / 'leanchecker'), '--from-export'],
    [str(lean_bin / 'con-ron'), '--verified', '--jobs=1'],
]
for i, cmd in enumerate(checkers):
    run(cmd + [str(OUT / 'proofs.ndjson')], log=f'kernel-{i}-positive.log', contains=('accept',))
print('Lean kernel + independent Con-Ron kernel accept all six theorems, with no axioms', flush=True)


# Submit well-formed but ill-typed proofs directly to both kernels.
exprs = {r['ie']: r for r in records if 'ie' in r}
control = next(r for r in records if 'thm' in r
               and names[r['thm']['name']] == 'FormatFacts.kernel_control')
false_expr = next(r['ie'] for r in records if 'const' in r
                  and names[r['const']['name']] == 'False')
fresh = max(exprs) + 1
for kind in ['zero-equals-one', 'false']:
    mutated = []
    for r in records:
        if r is control:
            r = json.loads(json.dumps(r))
            if kind == 'zero-equals-one':
                mutated += [{'ie': fresh, 'natVal': '1'},
                            {'ie': fresh+1, 'app': {'fn': exprs[r['thm']['type']]['app']['fn'], 'arg': fresh}}]
                r['thm']['type'] = fresh+1  # Eq Nat 0 1, retaining the proof Eq.refl 0.
            else:
                r['thm']['type'] = false_expr  # False, retaining the same proof.
        mutated.append(r)
    path = OUT / (kind + '.ndjson')
    path.write_text(''.join(json.dumps(r) + '\n' for r in mutated))
    for i, cmd in enumerate(checkers):
        run(cmd + [str(path)], log=f'kernel-{i}-{kind}.log', reject=True,
            contains=('type mismatch', 'FormatFacts.kernel_control'))
print('Both proof kernels reject 0 = 1 and False proved with Eq.refl 0', flush=True)
decls = sum(any(k in r for k in ['def', 'thm', 'opaque', 'axiom', 'inductive', 'quot']) for r in records)
print(f'Export closure: {decls} declaration records, {len(export.splitlines())} lines, {len(export.encode())} bytes')
for p in sorted((ROOT / 'verification').glob('*')) + [ROOT / 'Proofs/FormatFacts.lean', ROOT / 'Proofs.lean', ROOT / 'check']:
    if p.is_file():
        data = p.read_bytes()
        print(f'Review size: {p.relative_to(ROOT)}: {len(data.splitlines())} lines, {len(data)} bytes')
print('PASS: R1, R2, R3 REFUTED; independent replays and negative controls passed')
