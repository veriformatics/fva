#!/usr/bin/env python3
"""A test-only copy: wrap every linear-memory access with an R1 byte check."""
from pathlib import Path
import re
import subprocess

out = Path('verification/out')
out.mkdir(exist_ok=True)
wat = subprocess.check_output(['wasm-tools', 'print', 'lz4-c.wasm'], text=True)
assert len(re.findall(r'^  \(func ', wat, re.M)) == 6
assert len(re.findall(r'^  \(global ', wat, re.M)) == 1
# Append functions, so all original function indices remain unchanged.
pattern = re.compile(r'^(\s+)((i32|i64)\.(load|store)(?:8_[su]|16_[su]|32_[su]|8|16|32)?)([^\n]*)$', re.M)
wrappers = []
cache = {}

def replace(match):
    indent, op, typ, direction, attrs = match.groups()
    key = op + attrs
    if key not in cache:
        index = 7 + len(wrappers)  # function 6 is the guard
        cache[key] = index
        width_match = re.search(r'(?:load|store)(\d+)', op)
        width = int(width_match[1]) // 8 if width_match else (4 if typ == 'i32' else 8)
        offset_match = re.search(r'offset=(\d+)', attrs)
        offset = int(offset_match[1]) if offset_match else 0
        store = direction == 'store'
        signature = f'(param i32 {typ})' if store else f'(param i32) (result {typ})'
        original = f'local.get 0\n' + ('local.get 1\n' if store else '') + key
        wrappers.append(f'''(func {signature}
          local.get 0 i64.extend_i32_u i64.const {offset} i64.add
          i32.const {width} i32.const {int(store)} call 6
          {original})''')
    return indent + f'call {cache[key]}'

instrumented = pattern.sub(replace, wat)
assert cache and not pattern.search(instrumented)
guard = '''
(global $src (mut i32) (i32.const 0))
(global $dst (mut i32) (i32.const 0))
(global $size (mut i32) (i32.const 0))
(global $cap (mut i32) (i32.const 0))
(func (param $addr i64) (param $n i32) (param $write i32)
 (local $p i64)
 (loop $next
   local.get $addr local.set $p
   local.get $p i64.const 131072 i64.ge_u
   local.get $p i64.const 2097152 i64.lt_u i32.and
   if
     local.get $p global.get $dst i64.extend_i32_u i64.ge_u
     local.get $p global.get $dst global.get $cap i32.add i64.extend_i32_u i64.lt_u
     i32.and
     local.get $write i32.eqz
     local.get $p global.get $src i64.extend_i32_u i64.ge_u
     local.get $p global.get $src global.get $size i32.add i64.extend_i32_u i64.lt_u
     i32.and i32.and i32.or i32.eqz
     if unreachable end
   end
   local.get $addr i64.const 1 i64.add local.set $addr
   local.get $n i32.const 1 i32.sub local.tee $n br_if $next))
'''
setter = '''(func (export "set_bounds") (param i32 i32 i32 i32)
 local.get 0 global.set $src local.get 1 global.set $dst
 local.get 2 global.set $size local.get 3 global.set $cap)'''
# Wasm indices count functions, not text order of global fields.
assert instrumented.rstrip().endswith(')')
text = instrumented.rstrip()[:-1] + guard + '\n'.join(wrappers) + setter + ')\n'
(out / 'guarded.wat').write_text(text)
subprocess.run(['wasm-tools', 'parse', str(out / 'guarded.wat'), '-o', str(out / 'guarded.wasm')], check=True)
subprocess.run(['wasm-tools', 'validate', str(out / 'guarded.wasm')], check=True)
print(f'R1 instrumentation: {len(cache)} access forms, {len(pattern.findall(wat))} sites wrapped')
