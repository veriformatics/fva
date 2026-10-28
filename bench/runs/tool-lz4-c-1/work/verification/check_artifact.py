#!/usr/bin/env python3
"""Finite differential tests of exact Wasm bytes; NOT a universal proof."""
from pathlib import Path
import hashlib
import random
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
generated = tempfile.TemporaryDirectory(prefix='lz4-check-')
OUT = Path(generated.name)
EXPECTED = '8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6'
blob = (ROOT / 'lz4-c.wasm').read_bytes()
assert len(blob) == 8469 and hashlib.sha256(blob).hexdigest() == EXPECTED
subprocess.run(['wasm-tools', 'validate', str(ROOT / 'lz4-c.wasm')], check=True)
wat = subprocess.check_output(['wasm-tools', 'print', str(ROOT / 'lz4-c.wasm')], text=True)
assert '(memory (;0;) 32 32)' in wat
assert '(export "LZ4_decompress_safe" (func 2))' in wat

# Instrument each original memory instruction, including those inside memcpy etc.
# Function/global definitions are appended, preserving all original numeric indices.
# Original load/store immediates and value types are retained in their wrappers.
wrappers = {}
def instrument(m):
    instruction = m[0].strip()
    if instruction not in wrappers:
        op = instruction.split()[0]
        typ = op.split('.')[0]
        store = 'store' in op
        off = re.search(r'offset=(\d+)', instruction)
        off = int(off[1]) if off else 0
        width = re.search(r'(?:load|store)(\d+)', op)
        width = int(width[1]) // 8 if width else int(typ[1:]) // 8
        name = '$access' + str(len(wrappers))
        code = f'''(func {name} (param $a i32) {'(param $v ' + typ + ')' if store else ''}
          {'' if store else '(result ' + typ + ')'}
          local.get $a i32.const {2097152-off-width} i32.gt_u if unreachable end
          local.get $a i32.const {off} i32.add i32.const {width}
          i32.const {int(store)} call $guard
          local.get $a {'local.get $v' if store else ''} {instruction})'''
        wrappers[instruction] = name, code
    return '    call ' + wrappers[instruction][0]
pattern = r'^\s+i(?:32|64)\.(?:load(?:8_[su]|16_[su]|32_[su])?|store(?:8|16|32)?)(?: (?:offset|align)=\d+)*$'
inst, count = re.subn(pattern, instrument, wat, flags=re.M)
assert count > 0
# Fail rather than silently omit an instruction form the instrumenter does not know.
original_accesses = re.findall(r'^\s+(?:i(?:32|64)\.(?:load|store)\S*|memory\.(?:copy|fill|init|grow)).*$', wat, re.M)
assert len(original_accesses) == count
helpers = '''
(global $src (mut i32) (i32.const 0))
(global $sn (mut i32) (i32.const 0))
(global $dst (mut i32) (i32.const 0))
(global $dn (mut i32) (i32.const 0))
(func (export "bounds") (param i32 i32 i32 i32)
 local.get 0 global.set $src local.get 1 global.set $sn
 local.get 2 global.set $dst local.get 3 global.set $dn)
(func $guard (param $a i32) (param $n i32) (param $w i32)
 block $done loop $again
  local.get $n i32.eqz br_if $done
  local.get $a i32.const 131072 i32.lt_u
  local.get $a global.get $dst i32.ge_u
  local.get $a global.get $dst global.get $dn i32.add i32.lt_u i32.and i32.or
  local.get $w i32.eqz
  local.get $a global.get $src i32.ge_u
  local.get $a global.get $src global.get $sn i32.add i32.lt_u i32.and
  i32.and i32.or i32.eqz if unreachable end
  local.get $a i32.const 1 i32.add local.set $a
  local.get $n i32.const 1 i32.sub local.set $n br $again
 end end)
'''
inst = inst.rstrip()[:-1] + helpers + '\n'.join(c for _, c in wrappers.values()) + ')\n'
(OUT / 'instrumented.wat').write_text(inst)
subprocess.run(['wasm-tools', 'parse', str(OUT / 'instrumented.wat'), '-o', str(OUT / 'instrumented.wasm')], check=True)

# Independent byte-by-byte specification parser, accepting only R3's two relaxations.
# The caller decides whether to test R2's stronger end-of-block conditions.
def decode(data):
    p, out, matches, last_literals = 0, bytearray(), [], 0
    nonzero_offsets = True
    def length(base):
        nonlocal p
        if base != 15:
            return base
        while True:
            if p == len(data):
                raise ValueError('missing length terminator')
            b = data[p]
            p += 1
            base += b
            if b != 255:
                return base
    while p < len(data):
        token = data[p]
        p += 1
        n = length(token >> 4)
        if p + n > len(data):
            raise ValueError('truncated literals')
        out.extend(data[p:p+n])
        p += n
        if p == len(data):
            last_literals = n
            strict = nonzero_offsets and (not matches or (last_literals >= 5 and len(out)-matches[-1] >= 12))
            return bytes(out), strict
        if p + 2 > len(data):
            raise ValueError('truncated offset')
        offset = data[p] + 256*data[p+1]
        p += 2
        n = length(token & 15) + 4
        if offset > len(out):
            raise ValueError('offset before output')
        nonzero_offsets = nonzero_offsets and offset != 0
        matches.append(len(out))
        for _ in range(n):
            out.append(out[-offset] if offset else 0)
    raise ValueError('missing final sequence')

def enc_len(n):
    return bytes([255])*(n//255) + bytes([n%255])

def literals(b, low=0):
    return bytes([min(len(b), 15)*16 + low]) + (enc_len(len(b)-15) if len(b)>=15 else b'') + b

def sequence(b, offset, length):
    return (bytes([min(len(b), 15)*16+min(length-4, 15)])
            + (enc_len(len(b)-15) if len(b)>=15 else b'') + b
            + offset.to_bytes(2, 'little')
            + (enc_len(length-19) if length>=19 else b''))

rng = random.Random(0x4c5a34)
cases = []
def add(data, cap, category):
    try:
        expected, strict = decode(data)
    except ValueError:
        expected, strict = None, False
    # capacity==0 has the explicit implementation exception in README R2.
    required = expected is not None and strict and len(expected)<=cap and (cap>0 or data==b'\0')
    cases.append((data, cap, expected, required, category))

# Every one-byte input, at four output capacities (all byte values, not sampling).
for b in range(256):
    for cap in [0, 1, 14, 64]:
        add(bytes([b]), cap, 'one-byte')
for n in [0, 1, 4, 5, 12, 14, 15, 16, 18, 31, 32, 64, 254, 255, 269, 270, 271, 1024]:
    b = bytes(rng.randrange(256) for _ in range(n))
    for cap in sorted({0, max(0,n-1), n, n+1, n+40}):
        add(literals(b), cap, 'literal')
for offset in [0, 1, 2, 3, 4, 7, 8, 9, 15, 16, 255, 256, 65535]:
    b = bytes((i*37+11)%256 for i in range(offset))
    for ml in ([4, 19, 529] if offset == 65535 else [4, 7, 8, 12, 15, 18, 19, 20, 254, 274, 529]):
        for tail in ([5] if offset == 65535 else [0, 4, 5, 12]):
            data = sequence(b, offset, ml) + literals(b'abcde1234567'[:tail])
            size = len(b)+ml+tail
            for cap in [max(0,size-1), size, size+40]:
                add(data, cap, 'match')
# Truncations, invalid offsets, and deterministic random input.
for data in [b'', b'\x10', b'\xf0', b'\xf0\xff', b'\x00\x01\x00\x50abcde',
             b'\x0f\0\0\xff\xff\0\x50abcde']:
    for cap in [0, 1, 12, 32, 1024]:
        add(data, cap, 'malformed')
for _ in range(200):
    data = bytes(rng.randrange(256) for _ in range(rng.randrange(80)))
    add(data, rng.randrange(200), 'random')
# Multi-sequence blocks, including repetition whose match length exceeds offset.
for _ in range(150):
    data, produced = bytearray(), 0
    for j in range(rng.randrange(1,8)):
        b = bytes(rng.randrange(256) for _ in range(rng.randrange(1,25)))
        produced += len(b)
        offset = rng.randrange(1, min(produced,65535)+1)
        ml = rng.choice([4,7,8,18,19,20,270,529])
        data.extend(sequence(b, offset, ml))
        produced += ml
    data.extend(literals(bytes(rng.randrange(256) for _ in range(12))))
    produced += 12
    add(bytes(data), produced, 'multi')
    add(bytes(data), produced-1, 'multi')

# One compiled harness shared across the two target modules.
# Passive data initializes source immediately before each call. Output is initially
# nonzero to detect an incorrect zero-offset implementation. Compare every output
# byte on successful calls; on failure R2 requires success only for valid fitting input.
esc = lambda b: ''.join('\\%02x'%v for v in b)
parts = ['(module (import "target" "memory" (memory 32 32))',
         '(import "target" "LZ4_decompress_safe" (func $decode (param i32 i32 i32 i32) (result i32)))',
         '(import "target" "bounds" (func $bounds (param i32 i32 i32 i32)))']
checks = []
for i, (data,cap,expected,required,cat) in enumerate(cases):
    # Exercise both buffer orders and upper boundary placements, plus unaligned bases.
    src,dst = [(131073, 524289), (1048577, 131073),
               (min(2097151, 2097152-len(data)), 131073), (131073, min(2097151, 2097152-cap))][i%4]
    assert 131072 <= src <= 2097152 and 131072 <= dst <= 2097152
    assert src+len(data)<=2097152 and dst+cap<=2097152
    assert src+len(data)<=dst or dst+cap<=src
    scratch_end = 262144 + max(len(data), len(expected or b''))
    assert src+len(data)<=262144 or scratch_end<=src
    assert dst+cap<=262144 or scratch_end<=dst
    parts.append(f'(data $in{i} "{esc(data)}")')
    if expected is not None:
        parts.append(f'(data $out{i} "{esc(expected)}")')
    # Source preservation and destination guards are checked on every call.
    # Initialize all caller memory, permitting harmless source overcopies to be
    # distinguished from out-of-buffer accesses by the instrumented run.
    parts.append(f'''(func (export "t{i}") (result i32) (local $r i32) (local $j i32)
      i32.const 131072 i32.const 165 i32.const 1966080 memory.fill
      i32.const {src} i32.const 0 i32.const {len(data)} memory.init $in{i}
      i32.const {src} i32.const {len(data)} i32.const {dst} i32.const {cap} call $bounds
      i32.const {src} i32.const {dst} i32.const {len(data)} i32.const {cap} call $decode local.set $r
    ''')
    if required:
        parts.append('local.get $r i32.const 0 i32.lt_s if unreachable end')
    parts.append(f'local.get $r i32.const {cap} i32.gt_s if unreachable end')
    if expected is None:
        parts.append('local.get $r i32.const 0 i32.ge_s if unreachable end')
    else:
        parts.append('local.get $r i32.const 0 i32.ge_s if')
        parts.append(f'local.get $r i32.const {len(expected)} i32.ne if unreachable end')
        # Copy expected bytes to a scratch region disjoint from both buffers,
        # after decoding; compare every byte using a loop.
        if expected:
            parts.append(f"i32.const 262144 i32.const 0 i32.const {len(expected)} memory.init $out{i}")
            parts.append(f"""i32.const 0 local.set $j loop
              local.get $j i32.const {dst} i32.add i32.load8_u
              local.get $j i32.const 262144 i32.add i32.load8_u
              i32.ne if unreachable end
              local.get $j i32.const 1 i32.add local.tee $j
              i32.const {len(expected)} i32.lt_u br_if 0 end""")
        parts.append('end')
    if data:
        parts.append(f"i32.const 262144 i32.const 0 i32.const {len(data)} memory.init $in{i}")
        parts.append(f"""i32.const 0 local.set $j loop
          local.get $j i32.const {src} i32.add i32.load8_u
          local.get $j i32.const 262144 i32.add i32.load8_u
          i32.ne if unreachable end
          local.get $j i32.const 1 i32.add local.tee $j
          i32.const {len(data)} i32.lt_u br_if 0 end""")
    parts.append('i32.const 1)')
    checks.append(f'(assert_return (invoke "t{i}") (i32.const 1)) ;; {cat}')
parts.append(')')
harness = '\n'.join(parts)
# Original needs a no-op configuration export; supply it through a tiny adapter.
# The original module is embedded verbatim, with no changes whatsoever.
adapter = '''(module
(import "original" "memory" (memory 32 32))
(import "original" "LZ4_decompress_safe" (func $d (param i32 i32 i32 i32) (result i32)))
(export "memory" (memory 0)) (export "LZ4_decompress_safe" (func $d))
(func (export "bounds") (param i32 i32 i32 i32)))'''
script = f'(module binary "{esc(blob)}")\n(register "original")\n{adapter}\n(register "target")\n{harness}\n' + '\n'.join(checks)
script += f'\n{inst}\n(register "target")\n{harness}\n' + '\n'.join(checks) + '\n'
(OUT/'artifact-tests.wast').write_text(script)
print(f'Checking {len(cases)} cases on exact artifact and instrumented copy ({count} guarded instructions).', flush=True)
subprocess.run(['wasmtime','wast','-C','cache=n',str(OUT/'artifact-tests.wast')],check=True)
print(f'PASS: {2*len(cases)} concrete calls, including {sum(c[3] for c in cases)} required-success cases per module.')
