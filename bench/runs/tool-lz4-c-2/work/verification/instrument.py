#!/usr/bin/env python3
"""Add access guards for finite execution checks; this is not a proof."""
import hashlib
from pathlib import Path
import re
import subprocess
root = Path(__file__).resolve().parent.parent
assert hashlib.sha256((root/'lz4-c.wasm').read_bytes()).hexdigest() == '8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6'
wat = subprocess.check_output(['wasm-tools', 'print', str(root/'lz4-c.wasm')], text=True)
extra = ['(global $sb (mut i32) (i32.const 0))', '(global $se (mut i32) (i32.const 0))',
         '(global $db (mut i32) (i32.const 0))', '(global $de (mut i32) (i32.const 0))',
         '''(func (export "verify_config") (param i32 i32 i32 i32)
              local.get 0 global.set $sb local.get 1 global.set $se
              local.get 2 global.set $db local.get 3 global.set $de)''']
for kind in ('read', 'write'):
    def within(lo, hi):
        return f'local.get $p global.get ${lo} i64.extend_i32_u i64.ge_u local.get $q global.get ${hi} i64.extend_i32_u i64.le_u i32.and'
    permitted = within('db', 'de')
    if kind == 'read':
        permitted += ' ' + within('sb', 'se') + ' i32.or'
    extra.append(f'''(func ${kind}check (param $a i32) (param $off i32) (param $n i32) (result i32)
        (local $p i64) (local $q i64)
        local.get $a i64.extend_i32_u local.get $off i64.extend_i32_u i64.add local.tee $p
        local.get $n i64.extend_i32_u i64.add local.tee $q
        i64.const 131072 i64.le_u
        {permitted} i32.or i32.eqz if unreachable end local.get $a)''')
stores = {}
out = []
for line in wat.splitlines():
    m = re.fullmatch(r'(\s*)(i32\.(load8_u|load16_u|load|store8|store16|store))(.*)', line)
    if not m:
        out.append(line)
        continue
    indent, op, short, suffix = m.groups()
    width = 1 if '8' in short else 2 if '16' in short else 4
    offset = re.search(r'offset=(\d+)', suffix)
    offset = int(offset[1]) if offset else 0
    if short.startswith('load'):
        out.extend([f'{indent}i32.const {offset}', f'{indent}i32.const {width}', f'{indent}call $readcheck', line])
    else:
        key = op+suffix
        if key not in stores:
            name = '$store_checked_' + str(len(stores))
            stores[key] = name
            extra.append(f'''(func {name} (param i32 i32)
              local.get 0 i32.const {offset} i32.const {width} call $writecheck
              local.get 1 {key})''')
        out.append(indent + 'call ' + stores[key])
assert out[-1] == ')'
out[-1:-1] = extra
(root/'verification/guarded.wat').write_text('\n'.join(out)+'\n')
subprocess.run(['wasm-tools', 'parse', str(root/'verification/guarded.wat'), '-o', str(root/'verification/guarded.wasm')], check=True)
