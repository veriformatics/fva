#!/usr/bin/env python3
"""Generate only the import environment and callers; never alter edgeR.so."""
import hashlib
import pathlib
import re
import struct
import subprocess
import sys

out = pathlib.Path(sys.argv[1])
out.mkdir(parents=True, exist_ok=True)
artifact = pathlib.Path('edgeR.so').read_bytes()
assert len(artifact) == 96558
assert hashlib.sha256(artifact).hexdigest() == 'e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb'
wat = subprocess.check_output(['wasm-tools', 'print', 'edgeR.so'], text=True)
(out / 'edgeR.wat').write_text(wat)
# Audit the complete reached Wasm call graph: no hidden runtime dependency.
exports = dict(re.findall(r'\(export "([^"]+)" \(func (\d+)\)\)', wat))
host = dict(re.findall(r'\(import "env" "([^"]+)" \(func \(;(\d+);\)', wat))
for name in ['make_cmx', 'get_row', 'calc_cpm_raw']:
    body = wat.split(f'  (func (;{exports[name]};)', 1)[1].split('\n  (func ', 1)[0]
    assert not any(op in body for op in ['global.get', 'global.set', 'call_indirect', 'return_call'])
    allowed = {host['R_chk_calloc'], host['R_chk_free'], exports['get_row']} if name == 'calc_cpm_raw' else set()
    assert set(re.findall(r'^\s+call (\d+)', body, re.M)) <= allowed, name
env = ['(module', '(memory (export "memory") 32)',
       '(table (export "__indirect_function_table") 1024 funcref)',
       '(global $heap (mut i32) (i32.const 131072))',
       '(global (export "__stack_pointer") (mut i32) (i32.const 1048576))',
       '(global (export "__memory_base") i32 (i32.const 1024))',
       '(global (export "__table_base") i32 (i32.const 0))']
for line in wat.splitlines():
    m = re.fullmatch(r'  \(import "[^"]+" "([^"]+)" \(func .*', line)
    if m:
        name = m[1]
        sig = ' '.join(re.findall(r'\((?:param|result) [^)]*\)', line))
        body = 'unreachable'  # Any unexpected host call traps, including R errors.
        if name == 'R_chk_calloc':
            body = '''(local $p i32) global.get $heap local.tee $p
              local.get 0 local.get 1 i32.mul i32.add i32.const 7 i32.add
              i32.const -8 i32.and global.set $heap
              local.get $p i32.const 0 local.get 0 local.get 1 i32.mul memory.fill
              local.get $p'''
        if name == 'R_chk_free':
            body = 'nop'  # Fresh bounded runs; no reuse is needed.
        env.append(f'(func (export "{name}") {sig} {body})')
    m = re.fullmatch(r'  \(import "GOT\.(?:mem|func)" "([^"]+)" \(global .*', line)
    if m:
        env.append(f'(global (export "{m[1]}") (mut i32) (i32.const 0))')
env.append(')')
(out / 'env.wat').write_text('\n'.join(env))

# Column-major matrices. All inputs are exactly representable binary64 values.
cases = [([2.0**1023], [2.0**1023], 1, 1),
         ([1000000.0], [1000000.0], 1, 1),
         ([10., 8., 10., 8.], [18., 18.], 2, 2),
         ([11., 7., 11., 7.], [18., 18.], 2, 2),
         ([10.], [1000000.], 1, 1)]
wrapper = ['''(module
  (import "env" "memory" (memory 32))
  (import "edge" "make_cmx" (func $make (param i32 i32 i32 i32 i32 i32 i32)))
  (import "edge" "calc_cpm_raw" (func $cpm (param i32 i32 i32 i32)))''']
for k, (counts, libs, nr, nc) in enumerate(cases):
    wrapper.append(f'(func (export "case{k}") (param $i i32) (result i64)')
    for base, values in [(65600, counts), (65728, libs)]:
        for i, v in enumerate(values):
            wrapper.append(f'(f64.store (i32.const {base+8*i}) (f64.const {v.hex()}))')
    wrapper.append(f'''(call $make (i32.const 65536) (i32.const 65600) (i32.const 0)
      (i32.const {nr}) (i32.const {nc}) (i32.const 0) (i32.const 0))
    (call $make (i32.const 65568) (i32.const 65728) (i32.const 0)
      (i32.const {nr}) (i32.const {nc}) (i32.const 2) (i32.const 0))
    (call $cpm (i32.const 65536) (i32.const 65568) (i32.const 65600) (i32.const 1))
    (i64.load (i32.add (i32.const 65600) (i32.mul (local.get $i) (i32.const 8)))))''')
wrapper.append(')')
(out / 'caller.wat').write_text('\n'.join(wrapper))
for name in ['env', 'caller']:
    subprocess.run(['wasm-tools', 'parse', str(out / f'{name}.wat'),
                    '-o', str(out / f'{name}.wasm')], check=True)
subprocess.run(['wasm-tools', 'validate', 'edgeR.so'], check=True)
node = subprocess.check_output(['node', 'verification/run-wasm.mjs', str(out)], text=True)
print(node, end='')
expected = [0x7ff0000000000000, 0x412e848000000000, 0x4120f4471c71c71c]
for k, (counts, _, _, _) in enumerate(cases):
    observed = (out / f'case{k}.bin').read_bytes()
    assert len(observed) == 8*len(counts)
    for i in range(len(counts)):
        cmd = ['wasmtime', 'run', '-C', 'cache=n', '--preload', f'env={out}/env.wasm',
               '--preload', f'GOT.mem={out}/env.wasm',
               '--preload', f'GOT.func={out}/env.wasm',
               '--preload', 'edge=edgeR.so', '--invoke', f'case{k}',
               str(out / 'caller.wasm'), str(i)]
        p = subprocess.run(cmd, check=True, capture_output=True, text=True)
        bits = int(p.stdout.strip()) % (1 << 64)
        assert bits == struct.unpack_from('<Q', observed, 8*i)[0], (k, i)
    if k < 3:
        assert struct.unpack_from('<Q', observed)[0] == expected[k]
print('PASS: unmodified artifact, matching Wasmtime and V8 results for all 11 outputs')
