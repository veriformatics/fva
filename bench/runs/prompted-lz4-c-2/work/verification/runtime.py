"""Wasmtime cross-checks of the same case data used in the Lean statements."""
import json
from pathlib import Path


def make_wast(root, cases, wrong=False):
    binary = (root / 'lz4-c.wasm').read_bytes()
    escaped = ''.join(f'\\{b:02x}' for b in binary)
    lines = [f'(module $artifact binary "{escaped}")', '(register "artifact" $artifact)']
    lines += ['''(module $caller
      (import "artifact" "memory" (memory 32 32))
      (import "artifact" "LZ4_decompress_safe" (func $decode (param i32 i32 i32 i32) (result i32)))
      (func (export "fill") (param i32 i32 i32)
        local.get 0 local.get 1 local.get 2 memory.fill)
      (func (export "store") (param i32 i32)
        local.get 0 local.get 1 i32.store8)
      (func (export "load") (param i32) (result i32)
        local.get 0 i32.load8_u)
      (func (export "decode") (param i32 i32 i32 i32) (result i32)
        local.get 0 local.get 1 local.get 2 local.get 3 call $decode))''']
    for c in cases:
        src, dst, cap = c['src'], c['dst'], c['capacity']
        lines.append(f';; {c["name"]}')
        lines.append('(invoke $caller "fill" (i32.const 131072) (i32.const 0) (i32.const 1966080))')
        lines.append(f'(invoke $caller "fill" (i32.const {dst}) (i32.const 165) (i32.const {cap}))')
        for i, b in enumerate(c['input']):
            lines.append(f'(invoke $caller "store" (i32.const {src+i}) (i32.const {b}))')
        args = ' '.join(f'(i32.const {n})' for n in [src, dst, len(c['input']), cap])
        lines.append(f'(assert_return (invoke $caller "decode" {args}) (i32.const {c["result"]}))')
        for i, b in enumerate(c['output']):
            if wrong and c['name'] == 'literal':
                b = 66
            lines.append(f'(assert_return (invoke $caller "load" (i32.const {dst+i})) (i32.const {b}))')
        # Bytes of the source must be preserved; adjacent destination canaries too.
        for i, b in enumerate(c['input']):
            lines.append(f'(assert_return (invoke $caller "load" (i32.const {src+i})) (i32.const {b}))')
        for addr in [dst-1, dst+cap]:
            if 131072 <= addr < 2097152 and not src <= addr < src+len(c['input']):
                lines.append(f'(assert_return (invoke $caller "load" (i32.const {addr})) (i32.const 0))')
    return '\n'.join(lines) + '\n'
