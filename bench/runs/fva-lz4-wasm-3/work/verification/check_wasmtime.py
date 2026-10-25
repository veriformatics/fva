#!/usr/bin/env python3
"""Reproduce the Lean counterexamples on the unchanged binary with wasmtime wast."""
from hashlib import sha256
from pathlib import Path
import os
import subprocess
import tempfile

root = Path(__file__).resolve().parent.parent
wasm = (root / 'lz4-block-codec.wasm').read_bytes()
assert len(wasm) == 1226
assert sha256(wasm).hexdigest() == '4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf'
binary = ''.join(f'\\{b:02x}' for b in wasm)
input_bytes = b'abcdXabcd1234'
encoded = bytes.fromhex('50 61 62 63 64 58 05 00 40 31 32 33 34')
valid_block = bytes.fromhex('13 41 01 00 50 42 43 44 45 46')

# Check the format arithmetic for these particular witnesses (no general codec model).
assert encoded[0] >> 4 == 5 and encoded[0] & 15 == 0
assert encoded[1:6] == b'abcdX' and int.from_bytes(encoded[6:8], 'little') == 5
assert encoded[8] == 0x40 and encoded[9:] == b'1234'
assert len(encoded[9:]) == 4 < 5  # forbidden final literal count
assert len(input_bytes) - 5 == 8 < 12  # forbidden last-match position
assert valid_block[0] >> 4 == 1 and valid_block[0] & 15 == 3
assert valid_block[1:2] == b'A' and int.from_bytes(valid_block[2:4], 'little') == 1
assert valid_block[4] == 0x50 and valid_block[5:] == b'BCDEF'
decoded = b'A' + b'A' * (4 + (valid_block[0] & 15)) + valid_block[5:]
assert decoded == b'AAAAAAAABCDEF' and len(decoded) == 13
assert len(valid_block[5:]) == 5 and len(decoded) - 1 == 12


def stores(address, data):
    return '\n'.join(f'(i32.store8 (i32.const {address+i}) (i32.const {b}))'
                     for i, b in enumerate(data))


def byte_asserts(address, data):
    return '\n'.join(f'(assert_return (invoke "byte" (i32.const {address+i})) (i32.const {b}))'
                     for i, b in enumerate(data))


wast = f'''
(module $codec binary "{binary}")
(register "codec" $codec)
(module
  (import "codec" "memory" (memory 1))
  (import "codec" "lz4BlockEncode" (func $encode (param i32 i32 i32) (result i32)))
  (import "codec" "lz4BlockDecode" (func $decode (param i32 i32 i32) (result i32)))
  (func $reset
    (memory.fill (i32.const 0) (i32.const 0) (i32.shl (memory.size) (i32.const 16))))
  (func (export "byte") (param i32) (result i32) (i32.load8_u (local.get 0)))
  (func (export "r1") (result i32) (local $p i32)
    (drop (memory.grow (i32.const 4)))
    (call $reset)
    (loop $hash
      (i32.store (local.get $p) (i32.const -65536))
      (local.set $p (i32.add (local.get $p) (i32.const 4)))
      (br_if $hash (i32.lt_u (local.get $p) (i32.const 262144))))
    {stores(262144, input_bytes)}
    (call $encode (i32.const 262144) (i32.const 13) (i32.const 262200)))
  (func (export "r2") (result i32)
    (call $reset)
    {stores(100, valid_block)}
    (call $decode (i32.const 100) (i32.const 10) (i32.const 0)))
  (func (export "r3") (param $outside i32) (result i32)
    (call $reset)
    (i32.store8 (i32.const 1) (local.get $outside))
    (call $decode (i32.const 0) (i32.const 1) (i32.const 1024))))
(assert_return (invoke "r1") (i32.const 13))
{byte_asserts(262200, encoded)}
(assert_return (invoke "r2") (i32.const 1))
{byte_asserts(0, bytes([65]) + bytes(12))}
(assert_return (invoke "r3" (i32.const 0)) (i32.const 0))
(assert_return (invoke "r3" (i32.const 1)) (i32.const 4))
(module $edge binary "{binary}")
(assert_trap (invoke $edge "lz4BlockDecode" (i32.const 65535) (i32.const 1) (i32.const 0))
  "out of bounds memory access")
'''
with tempfile.TemporaryDirectory(prefix='lz4-witness-') as tmp:
    path = Path(tmp) / 'witnesses.wast'
    path.write_text(wast)
    subprocess.run(['wasmtime', 'wast', str(path)], check=True,
                   env=os.environ | {'XDG_CACHE_HOME': tmp})
print('PASS: R1 invalid encoder output; R2 short decode; R3 outside-byte dependence; empty-block trap')
