#!/usr/bin/env python3
"""Run concrete counterexamples against the exact shipped module, via WAST."""
from hashlib import sha256
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
ARTIFACT = ROOT / "lz4-block-codec.wasm"
EXPECTED = "4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf"


def wat_bytes(data):
    return '"' + ''.join(f'\\{b:02x}' for b in data) + '"'


def check_bytes(address, data):
    return '\n'.join(
        f'(assert_return (invoke "byte" (i32.const {address + i})) (i32.const {b}))'
        for i, b in enumerate(data)
    )


def run_case(directory, name, binary, body):
    path = directory / f"{name}.wast"
    path.write_text(
        f'(module $codec binary {wat_bytes(binary)})\n'
        '(register "codec" $codec)\n' + body
    )
    result = subprocess.run(
        ["wasmtime", "wast", "-C", "cache=n", str(path)], text=True, capture_output=True
    )
    if result.returncode:
        raise RuntimeError(f"{name} failed:\n{result.stdout}{result.stderr}")
    print(f"PASS {name}")


def main():
    binary = ARTIFACT.read_bytes()
    if len(binary) != 1226 or sha256(binary).hexdigest() != EXPECTED:
        raise RuntimeError("Shipped artifact size/hash differs from README")
    subprocess.run(["wasm-tools", "validate", str(ARTIFACT)], check=True)
    print(f"PASS artifact: {len(binary)} bytes, sha256 {EXPECTED}")
    with tempfile.TemporaryDirectory(prefix="lz4-verification-") as temp:
        directory = Path(temp)
        run_case(directory, "R1_late_match", binary, '''
(module
  (import "codec" "memory" (memory 1))
  (import "codec" "getLinearMemoryOffset" (func $base (result i32)))
  (import "codec" "lz4BlockEncodeBound" (func $bound (param i32) (result i32)))
  (import "codec" "lz4BlockEncode" (func $encode (param i32 i32 i32) (result i32)))
  (data $input "abcdabcd12345")
  (func (export "init") (result i32) (local $p i32)
    ;; Grow before initializing: table [0,262144), input [262144,262157),
    ;; output [262208,262237), all disjoint. The module initially has 1 page.
    (drop (memory.grow (i32.const 4)))
    (memory.init $input (i32.const 262144) (i32.const 0) (i32.const 13))
    (loop $fill
      (i32.store (local.get $p) (i32.const -65536))
      (local.set $p (i32.add (local.get $p) (i32.const 4)))
      (br_if $fill (i32.lt_u (local.get $p) (i32.const 262144))))
    (call $base))
  (func (export "bound") (result i32) (call $bound (i32.const 13)))
  (func (export "encode") (result i32)
    (call $encode (i32.const 262144) (i32.const 13) (i32.const 262208)))
  (func (export "byte") (param i32) (result i32) (i32.load8_u (local.get 0))))
(assert_return (invoke "init") (i32.const 0))
(assert_return (invoke "bound") (i32.const 29))
(assert_return (invoke "encode") (i32.const 13))
''' + check_bytes(262208, bytes.fromhex('40 61 62 63 64 04 00 50 31 32 33 34 35')))
        run_case(directory, "R2_early_return", binary, '''
(module
  (import "codec" "memory" (memory 1))
  (import "codec" "lz4BlockDecode" (func $decode (param i32 i32 i32) (result i32)))
  (data (i32.const 1024) "\\13a\\01\\00\\50bcdef")
  (data (i32.const 0) "?????????????")
  (func (export "decode") (result i32)
    (call $decode (i32.const 1024) (i32.const 10) (i32.const 0)))
  (func (export "byte") (param i32) (result i32) (i32.load8_u (local.get 0))))
(assert_return (invoke "decode") (i32.const 1))
''' + check_bytes(0, b'a????????????'))
        run_case(directory, "R3_empty_overread", binary, '''
(module
  (import "codec" "memory" (memory 1))
  (import "codec" "lz4BlockDecode" (func $decode (param i32 i32 i32) (result i32)))
  (data (i32.const 65535) "\\00")
  (func (export "pages") (result i32) (memory.size))
  (func (export "decode") (result i32)
    (call $decode (i32.const 65535) (i32.const 1) (i32.const 0))))
(assert_return (invoke "pages") (i32.const 1))
(assert_trap (invoke "decode") "out of bounds memory access")
''')
    print("All three requirements have reproducible counterexamples.")


if __name__ == "__main__":
    main()
