#!/usr/bin/env python3
"""WAST tests import the *original binary*, without compiling or rebuilding Rust."""
import json
import sys
from pathlib import Path
cases = json.loads(Path(sys.argv[1]).read_text())
blob = ''.join('\\%02x' % b for b in Path('lz4-flex.wasm').read_bytes())
lines = [f'(module $artifact binary "{blob}")', '(register "artifact" $artifact)']
for c in cases:
    lines += ['(module (import "artifact" "memory" (memory 32 32))',
              '(import "artifact" "lz4_decompress" (func $d (param i32 i32 i32 i32) (result i32)))',
              '(func (export "run") (result i32)',
              'i32.const 0 i32.const 204 i32.const 2097152 memory.fill']
    for i, b in enumerate(c['input']):
        lines += [f'i32.const {131072+i} i32.const {b} i32.store8']
    lines += [f'i32.const 131072 i32.const 262144 i32.const {len(c["input"])} i32.const {c["cap"]} call $d)',
              '(func (export "byte") (param i32) (result i32) local.get 0 i32.load8_u))',
              f'(assert_return (invoke "run") (i32.const {c["result"]}))']
    for i, b in enumerate(c['output']):
        lines += [f'(assert_return (invoke "byte" (i32.const {262144+i})) (i32.const {b}))']
Path(sys.argv[2]).write_text('\n'.join(lines)+'\n')
print(f'Wasmtime: generated {len(cases)} original-binary test cases')
