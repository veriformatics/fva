"""Bind the reviewed prefix model to the exact artifact instruction listing."""
from pathlib import Path
import hashlib
import re
import subprocess

root = Path(__file__).resolve().parent.parent
blob = (root / 'lz4-c.wasm').read_bytes()
assert hashlib.sha256(blob).hexdigest() == '8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6'
wat = subprocess.check_output(['wasm-tools', 'print', str(root / 'lz4-c.wasm')], text=True)
assert '(export "LZ4_decompress_safe" (func 2))' in wat
assert '(memory (;0;) 32 32)' in wat
body = wat.split('  (func (;2;)', 1)[1].split('  (func (;3;)', 1)[0]
lines = [re.sub(r';;.*', '', x).strip() for x in body.splitlines()[2:]]
lines = [x for x in lines if x]
expected = '''i32.const -1
local.set 4
block
local.get 0
i32.eqz
br_if 0
local.get 3
i32.const 0
i32.lt_s
br_if 0
block
local.get 3
br_if 0
local.get 2
i32.const 1
i32.ne
br_if 1
i32.const -1
i32.const 0
local.get 0
i32.load8_u
select
return
end
local.get 2
i32.eqz
br_if 0'''.splitlines()
# Branch target comments are not instructions.
lines = [re.sub(r'\s*\(;.*?;\)', '', x) for x in lines]
assert lines[:len(expected)] == expected, (lines[:len(expected)], expected)
assert lines[len(expected):len(expected)+3] == ['local.get 1', 'local.get 3', 'i32.add']
(root / 'verification/prefix.instructions').write_text('\n'.join(expected) + '\n')
print('Artifact prefix: all 27 instructions match the reviewed C model; tail starts with dst+cap.')
