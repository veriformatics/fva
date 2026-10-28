#!/usr/bin/env python3
"""Run the finite corpus on the UNCHANGED pinned binary using Wast assertions."""
import subprocess
import tempfile
import os
from pathlib import Path
from cases import CASES
from extract import module


def quote(data):
    return '"' + ''.join(f'\\{b:02x}' for b in data) + '"'


def script():
    raw, *_ = module()
    lines = [f'(module $artifact binary {quote(raw)})',
             '(register "artifact" $artifact)', '(module $tests',
             ' (import "artifact" "memory" (memory 32 32))',
             ' (import "artifact" "LZ4_decompress_safe"',
             '  (func $decode (param i32 i32 i32 i32) (result i32)))']
    for name, inp, cap, out, _ in CASES:
        lines += [f' (data ${name} {quote(inp)})',
                  f' (func (export "{name}") (result i32) (local $r i32)',
                  '  (memory.fill (i32.const 131072) (i32.const 165) (i32.const 1966080))',
                  f'  (memory.init ${name} (i32.const 131072) (i32.const 0) (i32.const {len(inp)}))',
                  f'  (local.set $r (call $decode (i32.const 131072) (i32.const 196608)',
                  f'    (i32.const {len(inp)}) (i32.const {cap})))']
        condition = '(i32.ge_s (local.get $r) (i32.const 0))' if out is None else (
            f'(i32.ne (local.get $r) (i32.const {len(out)}))')
        lines += [f'  (if {condition} (then (return (i32.const 0))))']
        for i, b in enumerate(out or []):
            lines += [f'  (if (i32.ne (i32.load8_u (i32.const {196608+i})) (i32.const {b}))',
                      '    (then (return (i32.const 0))))']
        # Check source preservation and the immediately adjacent destination guards.
        for addr, b in [(131072 + i, b) for i, b in enumerate(inp)] + [
                (196607, 165), (196608 + cap, 165)]:
            lines += [f'  (if (i32.ne (i32.load8_u (i32.const {addr})) (i32.const {b}))',
                      '    (then (return (i32.const 0))))']
        lines += ['  (i32.const 1))']
    lines += [')']
    for name, *_ in CASES:
        lines += [f'(assert_return (invoke $tests "{name}") (i32.const 1))']
    return '\n'.join(lines) + '\n'


if __name__ == '__main__':
    with tempfile.TemporaryDirectory(prefix='lz4-check-') as tmp:
        path = Path(tmp) / 'cases.wast'
        path.write_text(script())
        subprocess.run(['wasmtime', 'wast', str(path)], check=True,
                       env=os.environ | {'XDG_CACHE_HOME': tmp})
    print(f'PASS: {len(CASES)} unchanged-artifact Wasmtime executions')
