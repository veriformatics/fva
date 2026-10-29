#!/usr/bin/env python3
"""UNTRUSTED proof search: emit short execution equalities, all checked by kernels.

Unlike extract.py, this interpreter need not be trusted. Any wrong transition
makes its generated rfl proof fail. None of its state constants appear in the
statements of the exported verification claims.
"""
import copy
import json
import sys
from pathlib import Path
from extract import extract
ROOT = Path(__file__).resolve().parent.parent
_, OPS, LOCAL_COUNT = extract()
MOD = 1 << 32

def generate():
    cases = json.loads((ROOT/'verification/cases.json').read_text())
    lines = ['import Proofs.Claims', 'set_option maxRecDepth 1000000',
             'set_option maxHeartbeats 0', 'open Wasm', 'namespace Certificate']
    finals = {}
    for case in cases:
        name = case['name']
        lines.append('namespace '+name)
        m = {131072+i:b for i,b in enumerate(case['input'])}
        # No proved run reads module-private data: such a read is rejected below.
        s = dict(pc=0,stack=[],locals=[131072,262144,len(case['input']),case['cap']]+[0]*LOCAL_COUNT,
                 frames=[],status='running')
        mem_name, events_name = 'm0', 'e0'
        mi = ei = 0
        lines += [f'def m0 : Memory := Verification.inputMemory Samples.{name}.input',
                  'def e0 : List Event := []',
                  f'def s0 : State := initial Artifact.localCount 131072 262144 '
                  f'Samples.{name}.input.length Samples.{name}.cap m0']
        chunks, steps, chunk_start = [], 0, 0
        state_i = 0
        def event(write, a, n):
            nonlocal events_name, ei
            old = events_name
            ei += 1
            events_name = f'e{ei}'
            lines.append(f'def {events_name} : List Event := ⟨{str(write).lower()},{a},{n}⟩ :: {old}')
        def memory(expr):
            nonlocal mem_name, mi
            mi += 1
            mem_name = f'm{mi}'
            lines.append(f'def {mem_name} : Memory := {expr}')
        def pop():
            return s['stack'].pop(0)
        def push(v):
            s['stack'].insert(0,v)
        def branch(depth):
            f = s['frames'][depth]
            s['pc'] = f[0]
            s['stack'] = f[2].copy()
            s['frames'] = s['frames'][depth + (0 if f[1] else 1):]
        def state_text():
            frames = '['+', '.join('⟨'+f'{t},{str(loop).lower()},{saved}'+'⟩'
                                    for t,loop,saved in s['frames'])+']'
            status = '.running' if s['status']=='running' else '.returned '+str(s['status'])
            return ('{ pc := '+str(s['pc'])+', stack := '+str(s['stack'])+
                    ', locals := '+str(s['locals'])+', frames := '+frames+
                    f', mem := {mem_name}, events := {events_name}, status := {status}'+' }')
        while s['status'] == 'running':
            assert steps < case['fuel'], (name,'fuel exhausted')
            op,*args = OPS[s['pc']]
            pc = s['pc']
            s['pc'] += 1
            access = False
            if op in ('block','loop'):
                s['frames'].insert(0,(pc+1 if op=='loop' else args[0],op=='loop',s['stack'].copy()))
            elif op == 'end':
                s['frames'].pop(0)
            elif op == 'br':
                branch(args[0])
            elif op == 'brIf':
                if pop() != 0: branch(args[0])
            elif op == 'get': push(s['locals'][args[0]])
            elif op in ('set','tee'):
                v = pop(); s['locals'][args[0]] = v
                if op == 'tee': push(v)
            elif op == 'const': push(args[0])
            elif op == 'eqz': push(int(pop()==0))
            elif op == 'bin':
                b,a = pop(),pop()
                f = dict(eq=lambda:int(a==b),ne=lambda:int(a!=b),lt=lambda:int(a<b),
                         gt=lambda:int(a>b),le=lambda:int(a<=b),ge=lambda:int(a>=b),
                         add=lambda:(a+b)%MOD,sub=lambda:(a-b)%MOD,
                         band=lambda:a&b,shr=lambda:a>>(b%32))
                push(f[args[0]]())
            elif op == 'select':
                c,b,a = pop(),pop(),pop(); push(a if c else b)
            elif op in ('load','store'):
                width,offset = args
                if op == 'store': value = pop()
                address = pop()+offset
                assert 131072 <= address and address+width <= 2097152
                if op == 'load':
                    push(sum(m.get(address+i,0) << (8*i) for i in range(width)))
                else:
                    old = mem_name
                    memory(f'writeLE {old} {address} {value} {width}')
                    for i in range(width): m[address+i] = (value>>(8*i)) & 255
                event(op=='store',address,width)
                access = True
            elif op in ('copy','fill'):
                n,v,dst = pop(),pop(),pop()
                assert dst+n <= 2097152
                old = mem_name
                if op == 'copy':
                    assert v+n <= 2097152
                    payload = [m.get(v+i,0) for i in range(n)]
                    memory(f'copyBytes {old} {dst} {v} {n} {old}')
                    # Formal events are [write, read] prepended to the old trace.
                    event(False,v,n)
                else:
                    payload = [v%256]*n
                    memory(f'fillBytes {dst} {v} {n} {old}')
                for i,b in enumerate(payload): m[dst+i] = b
                event(True,dst,n)
                access = True
            elif op == 'ret':
                s['status'] = s['stack'][0]
                s['pc'] = pc
            else:
                raise AssertionError((name,pc,op))
            steps += 1
            if access or steps-chunk_start >= 1 or s['status'] != 'running':
                state_i += 1
                lines.append(f'def s{state_i} : State := '+state_text())
                size = steps-chunk_start
                lines.append(f'theorem h{state_i} : run Artifact.code {size} '
                             f's{state_i-1} = s{state_i} := rfl')
                chunks.append(size)
                chunk_start = steps
        assert s['status'] == case['result'] % MOD
        assert [m.get(262144+i,0) for i in range(len(case['output']))] == case['output']
        def compose(lo,hi):
            if hi-lo == 1: return f'h{hi}'
            mid = (lo+hi)//2
            return (f'(run_join Artifact.code {sum(chunks[lo:mid])} {sum(chunks[mid:hi])} '
                    f's{lo} s{mid} s{hi}\n {compose(lo,mid)}\n {compose(mid,hi)})')
        lines.append(f'theorem path : run Artifact.code {steps} s0 = s{state_i} := '+compose(0,state_i))
        lines.append(f'theorem replay : run Artifact.code {case["fuel"]} s0 = s{state_i} :=\n'
                     f'  run_join Artifact.code {steps} {case["fuel"]-steps} s0 s{state_i} s{state_i}\n'
                     f'    path (run_stopped _ _ _ (by decide))')
        finals[name] = f's{state_i}'
        lines += ['end '+name]
    lines += ['end Certificate','namespace Verification']
    for c in cases:
        name = c['name']
        lines += [f'theorem run_{name} : agrees Samples.{name} = true :=',
                  f'  agrees_of_execution _ Certificate.{name}.{finals[name]}',
                  f'    Certificate.{name}.replay (by rfl)']
    lines += ['end Verification','']
    return '\n'.join(lines)

if __name__ == '__main__':
    result = generate()
    target = ROOT/'Proofs/Traces.lean'
    if '--check' in sys.argv:
        assert target.read_text() == result
    else:
        target.write_text(result)
    print(f'untrusted proof certificates: {len(result.splitlines())} lines')
