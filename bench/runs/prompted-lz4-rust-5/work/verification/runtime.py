#!/usr/bin/env python3
"""Cross-check the sample outputs using Wasmtime on the unmodified artifact."""
import json
import subprocess
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent

def make_harness(cases, wrong=False):
    lines = ['(module',
             ' (import "artifact" "memory" (memory 32 32))',
             ' (import "artifact" "lz4_decompress" (func $decode (param i32 i32 i32 i32) (result i32)))',
             ' (func (export "check") (result i32)']
    def check(expr, expected):
        lines.append(f' (if (i32.ne {expr} (i32.const {expected})) (then unreachable))')
    for index, c in enumerate(cases):
        lines.append(' (memory.fill (i32.const 131072) (i32.const 0) (i32.const 1966080))')
        for i, b in enumerate(c['input']):
            lines.append(f' (i32.store8 (i32.const {131072+i}) (i32.const {b}))')
        for i in range(16):
            for a in [262144-16+i,262144+c['cap']+i]:
                lines.append(f' (i32.store8 (i32.const {a}) (i32.const 165))')
        expected = c['result'] + (1 if wrong and index == 0 else 0)
        check(f'(call $decode (i32.const 131072) (i32.const 262144) '
              f'(i32.const {len(c["input"])}) (i32.const {c["cap"]}))', expected)
        for i, b in enumerate(c['output']):
            check(f'(i32.load8_u (i32.const {262144+i}))',b)
        for i, b in enumerate(c['input']):
            check(f'(i32.load8_u (i32.const {131072+i}))',b)
        for i in range(16):
            for a in [262144-16+i,262144+c['cap']+i]:
                check(f'(i32.load8_u (i32.const {a}))',165)
    lines += [f' (i32.const {len(cases)})))', '']
    return '\n'.join(lines)

def check_runtime(out):
    cases = json.loads((ROOT/'verification/cases.json').read_text())
    for wrong in [False,True]:
        name = 'runtime-bad' if wrong else 'runtime'
        wat, wasm = out/(name+'.wat'), out/(name+'.wasm')
        wat.write_text(make_harness(cases,wrong))
        subprocess.run(['wasm-tools','parse',str(wat),'-o',str(wasm)],check=True)
        p = subprocess.run(['wasmtime','-C','cache=n','--preload',f'artifact={ROOT / "lz4-flex.wasm"}',
                            '--invoke','check',str(wasm)],capture_output=True,text=True)
        (out/(name+'.log')).write_text(p.stdout+p.stderr)
        if wrong:
            assert p.returncode != 0 and 'unreachable' in p.stderr, p.stderr
        else:
            assert p.returncode == 0 and p.stdout.strip() == str(len(cases)), p.stdout+p.stderr
    print(f'Wasmtime: {len(cases)} exact return/content/guard checks; wrong expectation rejected',flush=True)
