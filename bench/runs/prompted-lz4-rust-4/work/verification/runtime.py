#!/usr/bin/env python3
"""Independently run the proof corpus against the unmodified binary in Wasmtime."""
import json
import subprocess
from pathlib import Path

outdir = Path('verification/generated')
outdir.mkdir(exist_ok=True)
cases = json.loads(subprocess.check_output(['lake','env','lean','--run','verification/Emit.lean']))
artifact = Path('lz4-flex.wasm').read_bytes()
def quoted(data):
    return '"' + ''.join('\\%02x'%b for b in data) + '"'
lines = []
for i, c in enumerate(cases):
    lines += ['(module $artifact binary '+quoted(artifact)+')', '(register "artifact" $artifact)']
    lines += ['''(module $test
      (import "artifact" "memory" (memory 32 32))
      (import "artifact" "lz4_decompress" (func $d (param i32 i32 i32 i32) (result i32)))
      (data (i32.const %d) %s)
      (func (export "run") (result i32)
        i32.const %d i32.const 204 i32.const %d memory.fill
        i32.const %d i32.const %d i32.const %d i32.const %d call $d)
      (func (export "byte") (param i32) (result i32) local.get 0 i32.load8_u))'''
      % (c['src'],quoted(c['input']),c['dst'],c['cap'],c['src'],c['dst'],len(c['input']),c['cap'])]
    expected = c['expected']
    result = -1 if expected is None else len(expected)
    lines += ['(assert_return (invoke $test "run") (i32.const %d))'%result]
    for j,b in enumerate(expected or []):
        lines += ['(assert_return (invoke $test "byte" (i32.const %d)) (i32.const %d))'%(c['dst']+j,b)]
wast = outdir/'corpus.wast'
wast.write_text('\n'.join(lines)+'\n')
subprocess.run(['wasmtime','wast','-C','cache=n',str(wast)],check=True)
# Check the harness itself rejects an incorrect return on the real binary.
bad = outdir/'wrong-return.wast'
bad.write_text('\n'.join(lines[:3])+'\n(assert_return (invoke $test "run") (i32.const 0))\n')
negative = subprocess.run(['wasmtime','wast','-C','cache=n',str(bad)],capture_output=True,text=True)
assert negative.returncode != 0 and 'expected' in negative.stderr, negative
print(f'Wasmtime: {len(cases)} exact-binary cases and wrong-return negative control passed')
