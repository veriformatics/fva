#!/usr/bin/env python3
"""Run the original bytes in Wasmtime, checking return values and output bytes."""
import json, pathlib, sys
cases = json.loads(pathlib.Path('verification/cases.json').read_text())
def quoted(data):
    return '"'+''.join('\\%02x'%b for b in data)+'"'
lines = ['(module $artifact binary '+quoted(pathlib.Path('lz4-flex.wasm').read_bytes())+')',
         '(register "artifact" $artifact)']
for c in cases:
    lines += ['(module', '(import "artifact" "memory" (memory 32 32))',
              '(import "artifact" "lz4_decompress" (func $decode (param i32 i32 i32 i32) (result i32)))',
              '(func (export "test") (result i32)',
              'i32.const 131072 i32.const 90 i32.const 1966080 memory.fill',
              f'i32.const {c["dst"]} i32.const 165 i32.const {c["cap"]} memory.fill']
    for i,b in enumerate(c['input']):
        lines.append(f'i32.const {c["src"]+i} i32.const {b} i32.store8')
    lines += [f'i32.const {c["src"]} i32.const {c["dst"]} i32.const {len(c["input"])} i32.const {c["cap"]} call $decode)',
              '(func (export "read") (param i32) (result i32) local.get 0 i32.load8_u))']
    expected = c['expected']
    lines += [f'(assert_return (invoke "test") (i32.const {-1 if expected is None else len(expected)}))']
    if expected is not None:
        for i,b in enumerate(expected):
            lines.append(f'(assert_return (invoke "read" (i32.const {c["dst"]+i})) (i32.const {b}))')
pathlib.Path(sys.argv[1]).write_text('\n'.join(lines)+'\n')
