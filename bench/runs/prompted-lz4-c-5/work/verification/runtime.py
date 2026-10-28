#!/usr/bin/env python3
"""Run the unchanged binary in Wasmtime with independent result/output assertions."""
from pathlib import Path
import json, subprocess, sys
cases=json.loads(Path('verification/cases.json').read_text())
raw=Path('lz4-c.wasm').read_bytes()
def quoted(bs): return '"'+''.join(f'\\{x:02x}' for x in bs)+'"'
script=[]
for i,c in enumerate(cases):
    src,dst=131072,262144
    script += [f'(module $artifact{i} binary {quoted(raw)})',f'(register "artifact{i}" $artifact{i})',
        f'(module $test{i}',f'  (import "artifact{i}" "memory" (memory 32 32))',
        f'  (import "artifact{i}" "LZ4_decompress_safe" (func $decode (param i32 i32 i32 i32) (result i32)))',
        f'  (data (i32.const {src}) {quoted(c["input"])})',
        f'  (data (i32.const {dst}) {quoted([165]*c["cap"])})',
        '  (func (export "check") (result i32)',
        f'    i32.const {src} i32.const {dst} i32.const {len(c["input"])} i32.const {c["cap"]}',
        f'    call $decode i32.const {c["result"]} i32.eq']
    for k,v in enumerate(c['output']):
        script += [f'    i32.const {dst+k} i32.load8_u i32.const {v} i32.eq i32.and']
    script+=['  ))',f'(assert_return (invoke $test{i} "check") (i32.const 1))']
out=Path('verification/runtime.wast');out.write_text('\n'.join(script)+'\n')
subprocess.run(['wasmtime','wast','-C','cache=n',str(out)],check=True)
print(f'Wasmtime: {len(cases)} exact-artifact result/output checks passed',flush=True)
