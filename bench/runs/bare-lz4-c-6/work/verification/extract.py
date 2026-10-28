#!/usr/bin/env python3
"""Fail-closed extraction of reachable Wasm code into Proofs/Artifact.lean.
No C compiler, decompiler, or WAT parser is involved. --check compares bytes.
"""
import hashlib
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
EXPECTED = '8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6'

class Reader:
    def __init__(self, data):
        self.data, self.pos = data, 0
    def byte(self):
        b = self.data[self.pos]
        self.pos += 1
        return b
    def take(self, n):
        end = self.pos + n
        assert end <= len(self.data)
        b = self.data[self.pos:end]
        self.pos = end
        return b
    def uleb(self):
        v, shift = 0, 0
        while True:
            b = self.byte()
            v |= (b & 127) << shift
            if b < 128:
                return v
            shift += 7
            assert shift <= 35
    def sleb(self):
        v, shift = 0, 0
        while True:
            b = self.byte()
            v |= (b & 127) << shift
            shift += 7
            if b < 128:
                return v - (1 << shift) if b & 64 else v
            assert shift <= 35
    def name(self):
        return self.take(self.uleb()).decode()
    def done(self):
        assert self.pos == len(self.data)

BIN = {0x6a:'add', 0x6b:'sub', 0x71:'and', 0x73:'xor', 0x74:'shl',
       0x76:'shr_u', 0x46:'eq', 0x47:'ne', 0x48:'lt_s', 0x49:'lt_u',
       0x4b:'gt_u', 0x4d:'le_u', 0x4f:'ge_u'}

def instructions(body):
    r = Reader(body)
    nlocals = 0
    for _ in range(r.uleb()):
        n, typ = r.uleb(), r.byte()
        assert typ == 0x7f
        nlocals += n
    code, labels, patches = [], [], []
    while r.pos < len(body):
        op = r.byte()
        if op in (2, 3):
            assert r.byte() == 0x40, 'nonempty block type'
            labels.append([op, len(code), None])
            code.append('.nop')
        elif op == 0x0b:
            if labels:
                labels.pop()[2] = len(code) + 1
                code.append('.nop')
            else:
                code.append('.ret')
                r.done()
        elif op in (0x0c, 0x0d):
            depth = r.uleb()
            assert depth < len(labels)
            patches.append((len(code), labels[-1-depth], op))
            code.append(None)
        elif op == 0x0f:
            code.append('.ret')
        elif op == 0x10:
            fn = r.uleb()
            assert fn in (3, 4), 'unexpected call target'
            code.append(f'.call {fn}')
        elif op in (0x20, 0x21, 0x22):
            code.append(f'.{ {0x20:"get",0x21:"set",0x22:"tee"}[op]} {r.uleb()}')
        elif op == 0x41:
            code.append(f'.const {r.sleb() % 2**32}')
        elif op in BIN:
            code.append(f'.bin .{BIN[op]}')
        elif op == 0x45:
            code.append('.eqz')
        elif op in (0x1a, 0x1b):
            code.append('.drop' if op == 0x1a else '.select')
        elif op in (0x28, 0x2d, 0x2f, 0x36, 0x3a):
            align, offset = r.uleb(), r.uleb()
            width = {0x28:4, 0x2d:1, 0x2f:2, 0x36:4, 0x3a:1}[op]
            assert align <= (width.bit_length()-1)
            code.append(f'.{"load" if op < 0x36 else "store"} {width} {offset}')
        else:
            raise ValueError(f'unsupported opcode {op:#x}')
    assert not labels
    for idx, label, op in patches:
        dest = label[1]+1 if label[0] == 3 else label[2]
        assert dest is not None
        code[idx] = f'.{"jump" if op == 0x0c else "jumpIf"} {dest}'
    # Validate operand heights in the flattened CFG. All block/loop labels in
    # this module have empty entry stacks; no branch needs to discard operands.
    pending, heights = [(0,0)], {}
    while pending:
        pc, height = pending.pop()
        if pc in heights:
            assert heights[pc] == height
            continue
        assert 0 <= pc < len(code)
        heights[pc] = height
        fields = code[pc].split()
        kind = fields[0]
        need, delta = {
            '.nop':(0,0), '.const':(0,1), '.get':(0,1), '.set':(1,-1),
            '.tee':(1,0), '.bin':(2,-1), '.eqz':(1,0), '.select':(3,-2),
            '.drop':(1,-1), '.jump':(0,0), '.jumpIf':(1,-1),
            '.load':(1,0), '.store':(2,-2), '.call':(3,-2), '.ret':(1,0)
        }[kind]
        assert height >= need
        newheight = height + delta
        if kind == '.ret':
            assert height == 1
            continue
        if kind in ('.jump', '.jumpIf'):
            assert newheight == 0, 'branch would discard operand stack'
            pending.append((int(fields[1]),newheight))
        if kind != '.jump':
            pending.append((pc+1,newheight))
    return nlocals, code

def extract():
    raw = (ROOT/'lz4-c.wasm').read_bytes()
    assert len(raw) == 8469 and hashlib.sha256(raw).hexdigest() == EXPECTED
    r = Reader(raw)
    assert r.take(8) == b'\0asm\1\0\0\0'
    sections = {}
    while r.pos < len(raw):
        tag = r.byte()
        payload = r.take(r.uleb())
        assert tag not in sections and tag in (1,3,5,6,7,10,11)
        sections[tag] = Reader(payload)
    t = sections[1]
    types = []
    for _ in range(t.uleb()):
        assert t.byte() == 0x60
        ps = [t.byte() for _ in range(t.uleb())]
        rs = [t.byte() for _ in range(t.uleb())]
        assert set(ps) == {0x7f} and rs == [0x7f]
        types.append(len(ps))
    t.done()
    f = sections[3]
    ft = [f.uleb() for _ in range(f.uleb())]
    f.done()
    assert ft == [0,1,1,2,2,2] and types == [6,4,3]
    m = sections[5]
    assert [m.uleb() for _ in range(4)] == [1,1,32,32]
    m.done()
    g = sections[6]
    assert g.take(len(g.data)) == bytes.fromhex('017f01418080040b')
    ex = sections[7]
    exports = {}
    for _ in range(ex.uleb()):
        name = ex.name()
        exports[name] = (ex.byte(), ex.uleb())
    assert exports == {'memory':(2,0), 'LZ4_compress_default':(0,1), 'LZ4_decompress_safe':(0,2)}
    ex.done()
    data = sections[11]
    assert data.uleb() == 1 and data.uleb() == 0
    assert data.byte() == 0x41 and data.sleb() == 65536 and data.byte() == 0x0b
    table = data.take(data.uleb())
    data.done()
    c = sections[10]
    assert c.uleb() == 6
    bodies = [c.take(c.uleb()) for _ in range(6)]
    c.done()
    out = ['-- Generated by verification/extract.py from the SHA-256-pinned Wasm.\n',
           'import Proofs.Wasm\n\nnamespace Artifact\nopen Wasm\n\n']
    for fn in (2,3,4):
        nl, code = instructions(bodies[fn])
        def tree(lo,hi,indent):
            if hi-lo == 1:
                return f'if pc = {lo} then some ({code[lo]}) else none'
            mid = (lo+hi)//2
            pad = ' '*indent
            return (f'if pc < {mid} then\n'+pad+tree(lo,mid,indent+2)+
                    '\n'+' '*(indent-2)+'else\n'+pad+tree(mid,hi,indent+2))
        out += [f'def function{fn} : Func :=\n  ⟨{types[ft[fn]]}, {nl}, fun pc =>\n    ',
                tree(0,len(code),6), '\n  ⟩\n\n']
    out += ['def program : Program\n  | 2 => some function2\n  | 3 => some function3\n  | 4 => some function4\n  | _ => none\n\n',
            'def dataBytes : List Nat := [', ', '.join(map(str,table)), ']\n\n',
            'def initialByte (address : Nat) : Nat :=\n',
            '  if 65536 ≤ address && address < 65536 + dataBytes.length then\n',
            '    dataBytes[address - 65536]!\n  else 0\n\nend Artifact\n']
    text = ''.join(out)
    _, decoder = instructions(bodies[2])
    lemmas = 'set_option maxRecDepth 4096\n\n' + ''.join(f'@[simp] theorem fetch2_{pc} : fetch program 2 {pc} = some ({decoder[pc]}) := rfl\n' for pc in list(range(28)) + [580,581])
    return text.replace('end Artifact\n', lemmas + '\nend Artifact\n')

if __name__ == '__main__':
    target = ROOT/'Proofs/Artifact.lean'
    generated = extract()
    if sys.argv[1:] == ['--check']:
        assert target.read_text() == generated, 'artifact extraction differs'
        print('PASS: exact artifact SHA-256, structure, and generated instructions')
    else:
        assert not sys.argv[1:]
        target.write_text(generated)
        print('Wrote Proofs/Artifact.lean')
