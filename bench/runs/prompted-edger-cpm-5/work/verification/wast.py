#!/usr/bin/env python3
"""Embed the unchanged binary in a WAST test; supply a fail-closed host."""
from pathlib import Path
import re
import struct
import subprocess
import sys

out = Path(sys.argv[1])
wat = subprocess.check_output(['wasm-tools','print','edgeR.so'],text=True)
(out/'artifact.wat').write_text(wat)
host = ['(module $host', '(memory (export "memory") 32)',
        '(table (export "__indirect_function_table") 32 funcref)',
        '(global $heap (mut i32) (i32.const 131072))']
for line in wat.splitlines():
    if not line.startswith('  (import '):
        continue
    module, name = re.match(r'  \(import "([^"]+)" "([^"]+)"',line).groups()
    if '(func ' in line:
        sig = re.search(r'\(type \d+\)(.*?)\)\)$',line).group(1)
        if name == 'R_chk_calloc':
            body = '''(local $p i32) (local $n i32)
              local.get 0 local.get 1 i32.mul local.set $n
              global.get $heap local.tee $p
              local.get $n i32.const 7 i32.add i32.const -8 i32.and
              i32.add global.set $heap
              global.get $heap i32.const 900000 i32.ge_u if unreachable end
              local.get $p i32.const 0 local.get $n memory.fill local.get $p'''
        elif name == 'R_chk_free':
            body = ''
        else:
            body = 'unreachable'
        host.append(f'(func (export "{name}") {sig} {body})')
    elif '(global ' in line:
        mutable = '(mut i32)' if '(mut i32)' in line else 'i32'
        value = 1048576 if name == '__stack_pointer' else 1024 if name == '__memory_base' else 0
        host.append(f'(global (export "{name}") {mutable} (i32.const {value}))')
    else:
        assert name in ['memory','__indirect_function_table'], line
host += [')','(register "env" $host)','(register "GOT.mem" $host)',
         '(register "GOT.func" $host)']
# WAST binary form preserves every byte, including start, data, imports, and helpers.
binary = Path('edgeR.so').read_bytes()
host += ['(module $artifact binary']
host += ['"'+''.join(f'\\{b:02x}' for b in binary[i:i+1024])+'"'
         for i in range(0,len(binary),1024)]
host += [')','(register "artifact" $artifact)']
escaped = lambda bs: '"'+''.join(f'\\{b:02x}' for b in bs)+'"'
host += ['''(module $test
 (import "env" "memory" (memory 32))
 (import "artifact" "make_cmx" (func $make (param i32 i32 i32 i32 i32 i32 i32)))
 (import "artifact" "calc_cpm_raw" (func $raw (param i32 i32 i32 i32)))
 (func (export "cell") (param $c f64) (param $L f64) (result f64)
   i32.const 40000 local.get $c f64.store
   i32.const 50000 local.get $L f64.store
   i32.const 32768 i32.const 40000 i32.const 0 i32.const 1 i32.const 1 i32.const 0 i32.const 0 call $make
   i32.const 32800 i32.const 50000 i32.const 0 i32.const 1 i32.const 1 i32.const 0 i32.const 0 call $make
   i32.const 32768 i32.const 32800 i32.const 40000 i32.const 1 call $raw
   i32.const 40000 f64.load)
''', f'(data (i32.const 60000) {escaped(struct.pack("<4d",10,8,10,8))})',
f'(data (i32.const 61000) {escaped(struct.pack("<4d",18,18,18,18))})',
'''(func (export "matrix") (result i64 i64 i64 i64)
   i32.const 32768 i32.const 60000 i32.const 0 i32.const 2 i32.const 2 i32.const 0 i32.const 0 call $make
   i32.const 32800 i32.const 61000 i32.const 0 i32.const 2 i32.const 2 i32.const 0 i32.const 0 call $make
   i32.const 32768 i32.const 32800 i32.const 60000 i32.const 1 call $raw
   i32.const 60000 i64.load i32.const 60008 i64.load
   i32.const 60016 i64.load i32.const 60024 i64.load)
)
(assert_return (invoke $test "cell" (f64.const 0x1p+1020) (f64.const 0x1p+1020)) (f64.const inf))
(assert_return (invoke $test "cell" (f64.const 10) (f64.const 18)) (f64.const 0x1.0f4471c71c71cp+19))
(assert_return (invoke $test "matrix")
 (i64.const 0x4120f4471c71c71c) (i64.const 0x411b2071c71c71c7)
 (i64.const 0x4120f4471c71c71c) (i64.const 0x411b2071c71c71c7))
''']
script = '\n'.join(host)
(out/'artifact.wast').write_text(script)
# Known false execution claim: the exact same first invocation returns finite 1e6.
assert script.count('(f64.const inf)') == 1
(out/'false-artifact.wast').write_text(script.replace('(f64.const inf)','(f64.const 1000000)'))
print('WAST: embedded all',len(binary),'original artifact bytes')
