#!/usr/bin/env python3
"""Insert runtime range checks before each Wasm load/store (testing only)."""
import pathlib
import re
import subprocess
import sys

root = pathlib.Path(__file__).resolve().parent.parent
text = subprocess.check_output(['wasm-tools', 'print', str(root / 'lz4-c.wasm')], text=True)
# Two new imported functions precede all original defined functions.
text = re.sub(r'\(func (\d+)\)', lambda m: f'(func {int(m[1])+2})', text)
text = re.sub(r'\bcall (\d+)', lambda m: f'call {int(m[1])+2}', text)
text = text.replace('(module\n', '''(module
  (import "checks" "read" (func $checkRead (param i32 i32)))
  (import "checks" "write" (func $checkWrite (param i32 i32)))
''', 1)
lines = []
for line in text.splitlines():
    m = re.fullmatch(r'(\s+)(i32|i64)\.(load|store)(\d+)?(?:_[su])?(.*)', line)
    if m:
        pad, ty, action, bits, attributes = m.groups()
        width = int(bits or ty[1:]) // 8
        off = re.search(r'offset=(\d+)', attributes)
        offset = int(off[1]) if off else 0
        lines.extend([f'{pad}i32.const {width}', f'{pad}i32.const {offset}',
                      f'{pad}call ${action}_{ty}'])
    lines.append(line)
assert lines[-1] == ')'
helpers = []
for ty in ('i32', 'i64'):
    helpers += [f'''  (func $store_{ty} (param $a i32) (param $v {ty})
      (param $width i32) (param $offset i32) (result i32 {ty})
    local.get $a local.get $offset i32.add local.get $width call $checkWrite
    local.get $a local.get $v)''']
    helpers += [f'''  (func $load_{ty} (param $a i32) (param $width i32)
      (param $offset i32) (result i32)
    local.get $a local.get $offset i32.add local.get $width call $checkRead
    local.get $a)''']
out = '\n'.join(lines[:-1] + helpers + [')'])
subprocess.run(['wasm-tools', 'parse', '-o', sys.argv[1]], input=out, text=True, check=True)
print('Built instrumented test module (original artifact unchanged)')
