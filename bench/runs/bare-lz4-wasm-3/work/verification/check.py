#!/usr/bin/env python3
"""Replay counterexamples against the exact shipped bytes using Wasmtime WAST.

No source translation, instrumentation, external Python packages, or network.
The format facts about the constant byte strings are checked separately in Lean.
"""
import hashlib
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
ARTIFACT_SHA256 = "4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf"
FORMAT_SHA256 = "dce3c34a8738c44ed1dffb48c73e30297fca98ba7881408dc228865912c9a42e"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


artifact = (ROOT / "lz4-block-codec.wasm").read_bytes()
require(len(artifact) == 1226, "Artifact length changed")
require(hashlib.sha256(artifact).hexdigest() == ARTIFACT_SHA256, "Artifact hash changed")
require(hashlib.sha256((ROOT / "lz4_Block_format.md").read_bytes()).hexdigest()
        == FORMAT_SHA256, "Format document changed")
subprocess.run(["wasm-tools", "validate", str(ROOT / "lz4-block-codec.wasm")], check=True)

# The original binary is embedded verbatim in every independently instantiated test.
module = '(module $codec binary "' + ''.join(f'\\{b:02x}' for b in artifact) + '")\n'
module += '(register "codec" $codec)\n'
imports = '''
  (import "codec" "memory" (memory 1))
  (import "codec" "lz4BlockEncode" (func $encode (param i32 i32 i32) (result i32)))
  (import "codec" "lz4BlockDecode" (func $decode (param i32 i32 i32) (result i32)))
  (import "codec" "getLinearMemoryOffset" (func $base (result i32)))
  (func (export "byte") (param i32) (result i32) local.get 0 i32.load8_u)
  (func (export "word") (param i32) (result i32) local.get 0 i32.load)
  (func (export "poke") (param i32 i32) local.get 0 local.get 1 i32.store8)
'''


def wrapper(body):
    return '(module\n' + imports + body + ')\n'


def result(name, args, expected):
    operands = ''.join(f' (i32.const {n})' for n in args)
    return f'(assert_return (invoke "{name}"{operands}) (i32.const {expected}))\n'


encoder_block = bytes.fromhex('22 61 62 01 00 50 62 62 62 62 62')
encoder_input = b'a' + b'b' * 12
r1 = wrapper('''
  (func (export "run") (result i32) (local $p i32)
    ;; Five pages: table [0,262144), input [262144,262157), output [262160,...).
    i32.const 4 memory.grow drop
    call $base local.set $p
    block $done loop $fill
      local.get $p i32.const 262144 i32.ge_u br_if $done
      local.get $p i32.const -65536 i32.store
      local.get $p i32.const 4 i32.add local.set $p
      br $fill
    end end
    i32.const 262144 i32.const 0x62626261 i32.store
    i32.const 262148 i32.const 0x62626262 i32.store
    i32.const 262152 i32.const 0x62626262 i32.store
    i32.const 262156 i32.const 0x62 i32.store8
    i32.const 262144 i32.const 13 i32.const 262160 call $encode)
''')
r1 += result('run', [], 11)
for i, b in enumerate(encoder_block):
    r1 += result('byte', [262160 + i], b)
for i, b in enumerate(encoder_input):
    r1 += result('byte', [262144 + i], b)

# Same valid one-byte block and same arguments; only an out-of-block byte changes.
# No overlap: input [1024,1025), output [2048,2052).
empty = wrapper('''
  (data (i32.const 1024) "\\00\\00\\00")
  (data (i32.const 2047) "\\aa\\cc\\cc\\cc\\cc")
  (func (export "run") (result i32)
    i32.const 1024 i32.const 1 i32.const 2048 call $decode)
''')
empty += result('run', [], 0)
empty += result('word', [2048], -858993460)  # 0xcccccccc: untouched
empty += '(assert_return (invoke "poke" (i32.const 1025) (i32.const 1)))\n'
empty += result('run', [], 4)
empty += result('word', [2048], -1431655766)  # 0xaaaaaaaa: four unwanted writes
empty += result('byte', [1024], 0)  # compressed block is unchanged

# Nonempty valid block: one literal 'a', offset 1 / match length 7, then 'bcdef'.
# It expands to eight 'a' bytes followed by 'bcdef' (length 13).
nonempty = wrapper('''
  (data (i32.const 1024) "\\13\\61\\01\\00\\50\\62\\63\\64\\65\\66")
  (func (export "run") (result i32)
    i32.const 1024 i32.const 10 i32.const 0 call $decode)
''')
nonempty += result('run', [], 1)
nonempty += result('byte', [0], 97)
for i in range(1, 13):
    nonempty += result('byte', [i], 0)

# The valid empty block occupies the final byte of the initial one-page memory.
# Its output needs zero bytes; output 2048 is nonetheless comfortably in bounds.
trap = wrapper('''
  (data (i32.const 65535) "\\00")
  (func (export "run") (result i32)
    i32.const 65535 i32.const 1 i32.const 2048 call $decode)
''')
trap += '(assert_trap (invoke "run") "out of bounds memory access")\n'

cases = [
    ('r1-invalid-encoded-block', r1),
    ('r2-r3-empty-block-suffix-dependence', empty),
    ('r2-nonempty-block-output-before-input', nonempty),
    ('r2-r3-empty-block-boundary-trap', trap),
]
with tempfile.TemporaryDirectory(prefix='lz4-verification-') as directory:
    for name, body in cases:
        script = Path(directory) / (name + '.wast')
        script.write_text(module + body)
        subprocess.run(['wasmtime', 'wast', '-C', 'cache=n', str(script)], check=True)
        print('PASS ' + name, flush=True)
print('PASS exact artifact: ' + ARTIFACT_SHA256)
