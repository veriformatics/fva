#!/usr/bin/env python3
"""Add access checks to the decoder and its two reachable memory helpers.

This is runtime testing support, not part of the WP proof. No original function
indices change: new checkers, globals, and wrappers are appended to the module.
"""
from pathlib import Path
import hashlib
import re
import subprocess

root = Path(__file__).resolve().parent.parent
binary = root / 'lz4-c.wasm'
assert hashlib.sha256(binary.read_bytes()).hexdigest() == '8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6'
wat = subprocess.check_output(['wasm-tools', 'print', str(binary)], text=True)
wrappers = {}
lines = []
function = -1
for line in wat.splitlines():
    f = re.match(r'  \(func \(;(\d+);\)', line)
    if f:
        function = int(f[1])
    op = re.fullmatch(r'\s*(i32\.(load(?:8_u|16_u)?|store8?))((?: (?:offset|align)=\d+)*)\s*', line)
    if function in (2, 3, 4) and op:
        instruction = op[1] + op[3]
        if instruction not in wrappers:
            wrappers[instruction] = f'$access{len(wrappers)}'
        lines.append('    call ' + wrappers[instruction])
    else:
        lines.append(line)
wat = '\n'.join(lines)
assert wat.endswith(')')
extra = '''
  (global $s (mut i64) (i64.const 0))
  (global $se (mut i64) (i64.const 0))
  (global $d (mut i64) (i64.const 0))
  (global $de (mut i64) (i64.const 0))
  (func (export "bounds") (param i32 i32 i32 i32)
    local.get 0 i64.extend_i32_u global.set $s
    local.get 0 i64.extend_i32_u local.get 2 i64.extend_i32_u i64.add global.set $se
    local.get 1 i64.extend_i32_u global.set $d
    local.get 1 i64.extend_i32_u local.get 3 i64.extend_i32_u i64.add global.set $de)
  (func $check (param $a i64) (param $w i64) (param $write i32)
    (local $e i64)
    local.get $a local.get $w i64.add local.set $e
    ;; Entirely below caller memory is outside R1's observed address range.
    local.get $e i64.const 131072 i64.le_u
    if return end
    ;; Otherwise the complete access must be inside the source or destination.
    local.get $a global.get $d i64.ge_u
    local.get $e global.get $de i64.le_u i32.and
    local.get $write i32.eqz
    local.get $a global.get $s i64.ge_u
    local.get $e global.get $se i64.le_u i32.and i32.and i32.or
    if return end
    unreachable)
'''
for instruction, name in wrappers.items():
    op = instruction.split()[0]
    width = 1 if '8' in op else 2 if '16' in op else 4
    offset = re.search(r'offset=(\d+)', instruction)
    offset = int(offset[1]) if offset else 0
    write = 'store' in op
    extra += f'\n  (func {name} (param i32)' + (' (param i32)' if write else ' (result i32)') + '\n'
    extra += f'    local.get 0 i64.extend_i32_u i64.const {offset} i64.add\n'
    extra += f'    i64.const {width} i32.const {int(write)} call $check\n'
    extra += '    local.get 0\n' + ('    local.get 1\n' if write else '')
    extra += '    ' + instruction + ')\n'
out = root / 'verification' / 'instrumented.wat'
out.write_text(wat[:-1] + extra + ')\n')
subprocess.run(['wasm-tools', 'parse', str(out), '-o', str(out.with_suffix('.wasm'))], check=True)
subprocess.run(['wasm-tools', 'validate', str(out.with_suffix('.wasm'))], check=True)
print(f'Instrumented {len(wrappers)} distinct memory instructions in functions 2, 3 and 4')
