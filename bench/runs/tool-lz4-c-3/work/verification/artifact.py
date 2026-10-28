#!/usr/bin/env python3
"""Check identity, rebuild without overwriting the artifact, add access monitors."""
import hashlib
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
EXPECTED = '8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6'
data = (ROOT / 'lz4-c.wasm').read_bytes()
assert len(data) == 8469 and hashlib.sha256(data).hexdigest() == EXPECTED
subprocess.run(['wasm-tools', 'validate', str(ROOT / 'lz4-c.wasm')], check=True)
with tempfile.TemporaryDirectory() as tmp:
    p = Path(tmp)
    (p / 'src').symlink_to(ROOT / 'src', target_is_directory=True)
    subprocess.run(['bash', str(ROOT / 'build.sh')], cwd=p, check=True)
    assert (p / 'lz4-c.wasm').read_bytes() == data, 'Rebuild differs from artifact'
print('Artifact identity, validation, and byte-for-byte rebuild: PASS')
wat = subprocess.check_output(['wasm-tools', 'print', str(ROOT / 'lz4-c.wasm')], text=True)
helpers = []
ops = {}
pattern = re.compile(r'^(\s*)((?:i32|i64)\.(?:load|store)\S*)([^\n]*)$', re.M)

def replace(m):
    indent, op, options = m.groups()
    key = op + options.strip()
    if key not in ops:
        name = '$access_' + str(len(ops))
        ops[key] = name
        ty, action = op.split('.')
        width = 8 if ty == 'i64' else 4
        if '8' in action:
            width = 1
        elif '16' in action:
            width = 2
        offset = re.search(r'offset=(\d+)', options)
        offset = int(offset[1]) if offset else 0
        store = action.startswith('store')
        params = f'(param $a i32)' + (f' (param $v {ty})' if store else '')
        result = '' if store else f' (result {ty})'
        helpers.append(f'''(func {name} {params}{result}
          local.get $a
          i64.extend_i32_u
          i64.const {offset}
          i64.add
          i32.const {width}
          i32.const {int(store)}
          call $check_access
          local.get $a
          {'local.get $v' if store else ''}
          {op}{options})''')
    return indent + 'call ' + ops[key]

wat = pattern.sub(replace, wat)
monitor = '''
(global $source (mut i64) (i64.const 0))
(global $source_end (mut i64) (i64.const 0))
(global $dest (mut i64) (i64.const 0))
(global $dest_end (mut i64) (i64.const 0))
(func (export "set_bounds") (param $s i32) (param $d i32) (param $n i32) (param $c i32)
 local.get $s i64.extend_i32_u global.set $source
 global.get $source local.get $n i64.extend_i32_u i64.add global.set $source_end
 local.get $d i64.extend_i32_u global.set $dest
 global.get $dest local.get $c i64.extend_i32_u i64.add global.set $dest_end)
(func $check_access (param $a i64) (param $n i32) (param $write i32)
 (loop $again
   local.get $a i64.const 131072 i64.ge_u
   (if (then
     global.get $dest local.get $a i64.le_u
     local.get $a global.get $dest_end i64.lt_u i32.and
     global.get $source local.get $a i64.le_u
     local.get $a global.get $source_end i64.lt_u i32.and
     local.get $write i32.eqz i32.and
     i32.or i32.eqz (if (then unreachable))))
   local.get $a i64.const 1 i64.add local.set $a
   local.get $n i32.const 1 i32.sub local.tee $n br_if $again))
'''
# Append definitions: original numeric function/global indices remain unchanged.
pos = wat.rfind(')')
wat = wat[:pos] + monitor + '\n'.join(helpers) + wat[pos:]
with tempfile.TemporaryDirectory() as tmp:
    p = Path(tmp) / 'monitored.wat'
    p.write_text(wat)
    subprocess.run(['wasm-tools', 'parse', str(p), '-o', str(ROOT / 'verification/monitored.wasm')], check=True)
print(f'Access monitor prepared: {len(ops)} distinct load/store forms')
