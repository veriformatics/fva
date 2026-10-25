#!/usr/bin/env python3
"""Execute counterexamples against the hash-pinned, unmodified Wasm binary.

Only Python's standard library and wasm-tools/wasmtime are used. The generated
WAST embeds the binary verbatim; no WAT source or translated implementation is
executed. Pass --emit PATH to retain the complete test script for inspection.
"""
import argparse
import hashlib
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
ARTIFACT_SHA256 = "4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf"
R1_INPUT = b"abcdabcd12345"
R1_WIRE = bytes([64, 97, 98, 99, 100, 4, 0, 80, 49, 50, 51, 52, 53])
R2_WIRE = bytes([19, 97, 1, 0, 80, 97, 97, 97, 97, 97])


def quoted(data):
    return '"' + ''.join(f'\\{b:02x}' for b in data) + '"'


def codec(binary, name):
    return f'(module ${name} binary {quoted(binary)})\n(register "{name}" ${name})\n'


def byte_assertions(module, address, data):
    return ''.join(
        f'(assert_return (invoke ${module} "byte" (i32.const {address+i})) '
        f'(i32.const {b}))\n' for i, b in enumerate(data)
    )


def make_script(binary):
    script = codec(binary, 'codec1')
    stores = '\n'.join(
        f'(i32.store8 (i32.const {262144+i}) (i32.const {b}))'
        for i, b in enumerate(R1_INPUT)
    )
    script += f'''
(module $r1
  (import "codec1" "memory" (memory 1))
  (import "codec1" "lz4BlockEncode" (func $encode (param i32 i32 i32) (result i32)))
  (import "codec1" "lz4BlockDecode" (func $decode (param i32 i32 i32) (result i32)))
  (func (export "run") (result i32) (local $p i32)
    (drop (memory.grow (i32.const 5)))
    ;; Exactly 65,536 four-byte words, all initialized to -65536.
    (loop $initialize
      (i32.store (local.get $p) (i32.const -65536))
      (local.set $p (i32.add (local.get $p) (i32.const 4)))
      (br_if $initialize (i32.lt_u (local.get $p) (i32.const 262144))))
    {stores}
    (call $encode (i32.const 262144) (i32.const 13) (i32.const 300000)))
  (func (export "decode") (result i32)
    (call $decode (i32.const 300000) (i32.const 13) (i32.const 340000)))
  (func (export "byte") (param i32) (result i32) (i32.load8_u (local.get 0))))
(assert_return (invoke $r1 "run") (i32.const 13))
'''
    script += byte_assertions('r1', 300000, R1_WIRE)
    script += '(assert_return (invoke $r1 "decode") (i32.const 13))\n'
    script += byte_assertions('r1', 340000, R1_INPUT)
    script += codec(binary, 'codec2')
    script += f'''
(module $r2
  (import "codec2" "memory" (memory 1))
  (import "codec2" "lz4BlockDecode" (func $decode (param i32 i32 i32) (result i32)))
  (data (i32.const 1024) {quoted(R2_WIRE)})
  (func (export "run") (result i32)
    (memory.fill (i32.const 0) (i32.const 204) (i32.const 13))
    (call $decode (i32.const 1024) (i32.const 10) (i32.const 0)))
  (func (export "byte") (param i32) (result i32) (i32.load8_u (local.get 0))))
(assert_return (invoke $r2 "run") (i32.const 1))
'''
    script += byte_assertions('r2', 0, bytes([97] + [204] * 12))
    script += codec(binary, 'codec3')
    script += '''
(module $r3
  (import "codec3" "memory" (memory 1))
  (import "codec3" "lz4BlockDecode" (func $decode (param i32 i32 i32) (result i32)))
  (data (i32.const 65535) "\\00")
  (func (export "run") (result i32)
    (call $decode (i32.const 65535) (i32.const 1) (i32.const 0))))
(assert_trap (invoke $r3 "run") "out of bounds memory access")
'''
    # A second observation of R3, using entirely in-memory addresses: only
    # bytes outside the supplied empty block differ between the two calls.
    script += codec(binary, 'codec4')
    script += '''
(module $outside
  (import "codec4" "memory" (memory 1))
  (import "codec4" "lz4BlockDecode" (func $decode (param i32 i32 i32) (result i32)))
  (data (i32.const 1024) "\\00")
  (func (export "run") (param $outside i32) (result i32)
    (memory.fill (i32.const 0) (i32.const 0) (i32.const 65536))
    (i32.store16 (i32.const 1025) (local.get $outside))
    (i32.store8 (i32.const 4095) (i32.const 97))
    (memory.fill (i32.const 4096) (i32.const 204) (i32.const 13))
    (call $decode (i32.const 1024) (i32.const 1) (i32.const 4096)))
  (func (export "byte") (param i32) (result i32) (i32.load8_u (local.get 0))))
(assert_return (invoke $outside "run" (i32.const 0)) (i32.const 0))
(assert_return (invoke $outside "run" (i32.const 1)) (i32.const 4))
'''
    script += byte_assertions('outside', 4096, b'aaaa')
    return script


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--emit', type=Path)
    args = parser.parse_args()
    artifact = ROOT / 'lz4-block-codec.wasm'
    binary = artifact.read_bytes()
    if len(binary) != 1226 or hashlib.sha256(binary).hexdigest() != ARTIFACT_SHA256:
        raise SystemExit('FAIL: shipped artifact size/hash mismatch')
    subprocess.run(['wasm-tools', 'validate', str(artifact)], check=True)
    script = make_script(binary)
    if args.emit:
        args.emit.write_text(script)
    with tempfile.TemporaryDirectory(prefix='lz4-verification-') as directory:
        path = Path(directory) / 'counterexamples.wast'
        path.write_text(script)
        subprocess.run(['wasmtime', 'wast', '-C', 'cache=n', str(path)], check=True)
    print('PASS: exact 1226-byte artifact SHA-256 verified; Wasm validation succeeded')
    print('PASS R1 counterexample: encode returns 13 and the asserted nonconforming bytes')
    print('PASS R2 counterexample: valid 13-byte content is truncated to one byte')
    print('PASS R3 counterexample: valid empty block traps at the memory boundary')
    print('PASS R3 additional check: outside-block bytes change empty decode return 0 -> 4')
    print('All counterexample assertions passed. R1, R2, and R3 are FALSE.')


if __name__ == '__main__':
    main()
