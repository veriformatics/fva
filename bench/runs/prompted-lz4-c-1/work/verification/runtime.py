#!/usr/bin/env python3
"""Replay the kernel-checked examples on the original binary, without instrumentation."""
from pathlib import Path
import json, subprocess, sys, os
cases = json.loads(Path(sys.argv[1]).read_text())
outpath = Path(sys.argv[2])
binary = Path('lz4-c.wasm').read_bytes()
quote = lambda bs: '"'+''.join('\\%02x' % b for b in bs)+'"'
lines = ['(module $original binary '+quote(binary)+')', '(register "lz" $original)',
 '(module', ' (import "lz" "memory" (memory 32 32))',
 ' (import "lz" "LZ4_decompress_safe" (func $decode (param i32 i32 i32 i32) (result i32)))']

def eqcheck(expr, value):
    return f'  {expr} i32.const {value} i32.ne if unreachable end'

for n,c in enumerate(cases):
    lines += [f' (func (export "case{n}") (result i32)',
              f'  i32.const 131072 i32.const {c["fill"]} i32.const 1966080 memory.fill']
    for k,b in enumerate(c['input']):
        lines += [f'  i32.const {c["src"]+k} i32.const {b} i32.store8']
    call = ' '.join('i32.const '+str(v) for v in (c['src'], c['dst'], len(c['input']), c['cap']))+' call $decode'
    lines += [eqcheck(call,c['expected'])]
    if c['expected'] < 1 << 31:
        assert c['output'] is not None and len(c['output']) == c['expected']
        for k,b in enumerate(c['output']):
            lines += [eqcheck(f'i32.const {c["dst"]+k} i32.load8_u', b)]
    for k,b in enumerate(c['input']):
        lines += [eqcheck(f'i32.const {c["src"]+k} i32.load8_u', b)]
    # All locations immediately outside the destination, except the source, remain canaries.
    for addr in (c['dst']-1,c['dst']+c['cap']):
        if 131072 <= addr < 2097152 and not c['src'] <= addr < c['src']+len(c['input']):
            lines += [eqcheck(f'i32.const {addr} i32.load8_u',c['fill'])]
    lines += ['  i32.const 0)']
lines += [')']
for n in range(len(cases)):
    lines += [f'(assert_return (invoke "case{n}") (i32.const 0))']
outpath.write_text('\n'.join(lines)+'\n')
env = dict(os.environ, XDG_CACHE_HOME=str(outpath.parent / 'cache'))
subprocess.run(['wasmtime','wast',str(outpath)],check=True,env=env)
print(f'Wasmtime: {len(cases)} artifact executions passed (returns, decoded bytes, source and canaries)')
