#!/usr/bin/env python3
"""Generate a cache of parsed instructions. Lean rechecks every cached instruction."""
from pathlib import Path
p=Path('lz4-c.wasm').read_bytes()
def leb(i, signed=False):
    a=shift=0
    while True:
        b=p[i]; i+=1
        a|=(b&127)<<shift; shift+=7
        if b<128:
            if signed and b&64: a-=1<<shift
            return a,i
pos=8
while pos<len(p):
    tag=p[pos]; n,pos=leb(pos+1)
    if tag==10: break
    pos+=n
num,pos=leb(pos); bodies=[]
for _ in range(num):
    n,pos=leb(pos); bodies.append((pos,pos+n)); pos+=n
s='-- Generated cache; linkage theorems check it against the binary parser.\nimport Proofs.Binary\nset_option maxRecDepth 30000\nset_option maxHeartbeats 0\nnamespace Wasm\n'
for index in [2,3,4]:
    pos,stop=bodies[index]; ng,pos=leb(pos); count=0
    for _ in range(ng):
        n,pos=leb(pos); assert p[pos]==127;pos+=1;count+=n
    ops=[]
    while pos<stop:
        op=p[pos];pos+=1;a=b=0
        if op in [2,3]: assert p[pos]==64;pos+=1
        elif op in [12,13,16,32,33,34]: a,pos=leb(pos)
        elif op in [40,45,47,54,58]:
            b,pos=leb(pos);a,pos=leb(pos)
        elif op==65: a,pos=leb(pos,True);a%=2**32
        else: assert op in [11,15,26,27,69,70,71,72,73,75,77,79,106,107,113,115,116,118],op
        ops.append((op,a,b))
    # Small chunks avoid deeply nested elaborator terms.
    for off in range(0,len(ops),64):
        s+=f'def code{index}_{off//64} : List Instr := [\n'
        s+=',\n'.join(f'  ⟨{op},{a},{b}⟩' for op,a,b in ops[off:off+64])+'\n]\n'
    chunks=' ++ '.join(f'code{index}_{i}' for i in range((len(ops)+63)//64))
    s+=f'def cached{index} : Func := ⟨{count}, {chunks}⟩\n'
    s+=f'theorem linked{index} : parseFunction {index} = some cached{index} := by rfl\n'
s+='def function (i : Nat) : Option Func :=\n  if i == 2 then some cached2 else if i == 3 then some cached3 else if i == 4 then some cached4 else none\nend Wasm\n'
import sys
if '--check' in sys.argv:
    assert Path('Proofs/Code.lean').read_text() == s, 'generated file differs: Proofs/Code.lean'
else:
    Path('Proofs/Code.lean').write_text(s)
