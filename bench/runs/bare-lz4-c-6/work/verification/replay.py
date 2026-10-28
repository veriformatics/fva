#!/usr/bin/env python3
"""Run the pinned original bytes in Wasmtime, sharing its exported memory.
Concrete cases check returns, decoded contents and the entire caller-region
write frame. The small-input loop checks returns/content, not read footprints.
"""
import json
from pathlib import Path
import subprocess
import tempfile
import extract

ROOT = Path(__file__).resolve().parent.parent

def assertion(test):
    return f'{test}\nif unreachable end\n'

def driver(cases):
    out = ['''(module
(import "artifact" "memory" (memory 32 32))
(import "artifact" "LZ4_decompress_safe" (func $decode (param i32 i32 i32 i32) (result i32)))
(data (i32.const 4096) "\\00\\01\\02\\0c\\20\\40")
''']
    for i,c in enumerate(cases):
        src,dst,cap = c['src'],c['dst'],c['capacity']
        out.append(f'(func (export "case{i}") (result i32) (local $p i32)\n')
        out.append('i32.const 131072 i32.const 165 i32.const 1966080 memory.fill\n')
        for j,b in enumerate(c['input']):
            out.append(f'i32.const {src+j} i32.const {b} i32.store8\n')
        out.append(assertion(f'i32.const {src} i32.const {dst} i32.const {len(c["input"])} i32.const {cap} call $decode i32.const {c["expected"]} i32.ne'))
        if c['expected'] >= 0:
            assert len(c['output']) == c['expected']
            for j,b in enumerate(c['output']):
                out.append(assertion(f'i32.const {dst+j} i32.load8_u i32.const {b} i32.ne'))
        # Expected source bytes are constants, not guest-writable mirror memory.
        expected = 'i32.const 0'
        for j,b in reversed(list(enumerate(c['input']))):
            expected = (f'local.get $p i32.const {src+j} i32.eq '
                        f'if (result i32) i32.const {b} else {expected} end')
        # Every caller byte outside the destination must retain its initial value.
        out.append(f'''i32.const 131072 local.set $p
(loop $frame
  local.get $p i32.const {dst} i32.lt_u
  local.get $p i32.const {dst+cap} i32.ge_u i32.or
  if
    local.get $p i32.load8_u
    local.get $p i32.const {src} i32.ge_u
    local.get $p i32.const {src+len(c['input'])} i32.lt_u i32.and
    if (result i32)
      {expected}
    else i32.const 165 end
    i32.ne if unreachable end
  end
  local.get $p i32.const 1 i32.add local.tee $p
  i32.const 2097152 i32.lt_u br_if $frame)
i32.const 1)\n''')
    for size,count in [(0,1),(1,256),(2,65536)]:
        # Every byte string of this size, at six capacities. No compiler involved.
        out.append(f'''(func (export "small{size}") (result i32)
(local $i i32) (local $j i32) (local $cap i32) (local $want i32) (local $r i32)
(loop $inputs
  i32.const 131072 local.get $i i32.store16
  i32.const 0 local.set $j
  (loop $capacities
    local.get $j i32.load8_u offset=4096 local.set $cap
    i32.const 262128 i32.const 165 i32.const 96 memory.fill
''')
        if size == 0:
            out.append('i32.const -1 local.set $want\n')
        elif size == 1:
            out.append('''local.get $cap i32.eqz
if (result i32)
  local.get $i i32.eqz
  if (result i32) i32.const 0 else i32.const -1 end
else
  local.get $i i32.const 16 i32.lt_u
  if (result i32) i32.const 0 else i32.const -2 end
end local.set $want
''')
        else:
            out.append('''local.get $cap i32.eqz
if (result i32) i32.const -1
else
  local.get $i i32.const 240 i32.and i32.const 16 i32.eq
  if (result i32) i32.const 1 else i32.const -2 end
end local.set $want
''')
        out.append(f'''i32.const 131072 i32.const 262144 i32.const {size} local.get $cap
call $decode local.tee $r local.get $want i32.ne if unreachable end
local.get $r i32.const 1 i32.eq
if
  i32.const 262144 i32.load8_u
  local.get $i i32.const 8 i32.shr_u i32.ne if unreachable end
end
local.get $j i32.const 1 i32.add local.tee $j i32.const 6 i32.lt_u br_if $capacities)
local.get $i i32.const 1 i32.add local.tee $i i32.const {count} i32.lt_u br_if $inputs)
i32.const 1)
''')
    out.append(')\n')
    return ''.join(out)

def main():
    extract.extract()  # Check the exact module hash and supported structure.
    cases = json.loads((ROOT/'verification/cases.json').read_text())
    raw = (ROOT/'lz4-c.wasm').read_bytes()
    original = ''.join(f'\\{b:02x}' for b in raw)
    wast = f'(module $artifact binary "{original}")\n(register "artifact" $artifact)\n'
    wast += driver(cases)
    for i in range(len(cases)):
        wast += f'(assert_return (invoke "case{i}") (i32.const 1))\n'
    for n in range(3):
        wast += f'(assert_return (invoke "small{n}") (i32.const 1))\n'
    with tempfile.TemporaryDirectory() as td:
        path = Path(td)/'replay.wast'
        path.write_text(wast)
        subprocess.run(['wasmtime','wast','-C','cache=n',str(path)],check=True)
    print(f'PASS: Wasmtime original-byte replay of {len(cases)} cases, including full caller-region write frame')
    print('PASS: all 65,793 byte strings of length 0..2, capacities 0,1,2,12,32,64 (394,758 calls)')

if __name__ == '__main__':
    main()
