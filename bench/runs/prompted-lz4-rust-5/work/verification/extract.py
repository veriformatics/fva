#!/usr/bin/env python3
"""Decode the pinned module's actual function body; no Rust source is used."""
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SHA = '1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775'

class Reader:
    def __init__(self, data):
        self.data, self.pos = data, 0
    def byte(self):
        x = self.data[self.pos]
        self.pos += 1
        return x
    def take(self, n):
        assert self.pos + n <= len(self.data)
        x = self.data[self.pos:self.pos+n]
        self.pos += n
        return x
    def leb(self, signed=False):
        n, shift = 0, 0
        while True:
            b = self.byte()
            n |= (b & 127) << shift
            shift += 7
            assert shift <= 70
            if b < 128:
                return n - (1 << shift) if signed and b & 64 else n
    def name(self):
        return self.take(self.leb()).decode()
    def done(self):
        assert self.pos == len(self.data)

def extract():
    raw = (ROOT / 'lz4-flex.wasm').read_bytes()
    assert len(raw) == 7161 and hashlib.sha256(raw).hexdigest() == SHA
    r = Reader(raw)
    assert r.take(8) == b'\0asm\1\0\0\0'
    sections = {}
    while r.pos < len(raw):
        tag, size = r.byte(), r.leb()
        assert tag not in sections
        sections[tag] = r.take(size)
    assert 2 not in sections and 8 not in sections  # no imports or start function
    t = Reader(sections[1])
    types = []
    for _ in range(t.leb()):
        assert t.byte() == 0x60
        params = list(t.take(t.leb()))
        results = list(t.take(t.leb()))
        types.append((params, results))
    t.done()
    f = Reader(sections[3])
    function_types = [f.leb() for _ in range(f.leb())]
    f.done()
    m = Reader(sections[5])
    assert m.leb() == 1 and m.leb() == 1 and m.leb() == 32 and m.leb() == 32
    m.done()
    e = Reader(sections[7])
    exports = {}
    for _ in range(e.leb()):
        name = e.name()
        exports[name] = (e.byte(), e.leb())
    e.done()
    assert exports['memory'] == (2, 0)
    kind, index = exports['lz4_decompress']
    assert kind == 0 and types[function_types[index]] == ([127]*4, [127])
    c = Reader(sections[10])
    bodies = [c.take(c.leb()) for _ in range(c.leb())]
    c.done()
    assert len(bodies) == len(function_types)
    b = Reader(bodies[index])
    locals_ = []
    for _ in range(b.leb()):
        count, ty = b.leb(), b.byte()
        assert ty in (126, 127)
        locals_ += [ty] * count
    ops, opens = [], []
    unary = {0x45:'eqz'}
    binary = {0x46:'eq', 0x47:'ne', 0x49:'lt', 0x4b:'gt', 0x4d:'le',
              0x4f:'ge', 0x6a:'add', 0x6b:'sub', 0x71:'band', 0x76:'shr'}
    memory = {0x28:('load',4), 0x29:('load',8), 0x2d:('load',1),
              0x2f:('load',2), 0x36:('store',4), 0x37:('store',8),
              0x3a:('store',1), 0x3b:('store',2)}
    while b.pos < len(b.data):
        op = b.byte()
        if op in (2,3):
            assert b.byte() == 0x40  # all blocks have no parameters/results
            opens.append(len(ops))
            ins = ['block' if op == 2 else 'loop', 0]
        elif op == 0x0b:
            if opens:
                start = opens.pop()
                ops[start][1] = len(ops) + 1
                ins = ['end']
            else:
                ins = ['ret']
                assert b.pos == len(b.data)
        elif op in (0x0c,0x0d,0x10,0x20,0x21,0x22):
            ins = [{12:'br',13:'brIf',16:'call',32:'get',33:'set',34:'tee'}[op], b.leb()]
        elif op == 0x41:
            ins = ['const', b.leb(True) % (1 << 32)]
        elif op in memory:
            align, offset = b.leb(), b.leb()
            name, width = memory[op]
            assert 1 << align <= width
            ins = [name, width, offset]
        elif op == 0xfc:
            sub = b.leb()
            assert sub in (10,11) and b.leb() == 0
            if sub == 10:
                assert b.leb() == 0
            ins = ['copy' if sub == 10 else 'fill']
        elif op in unary:
            ins = [unary[op]]
        elif op in binary:
            ins = ['bin', binary[op]]
        else:
            assert op in (0,0x0f,0x1b), hex(op)
            ins = [{0:'trap',15:'ret',27:'select'}[op]]
        ops.append(ins)
    assert not opens
    # A call is deliberately unsupported by the formal evaluator. A proved
    # returning run cannot have passed one, so no callee is assumed correct.
    d = Reader(sections[11])
    data = []
    for _ in range(d.leb()):
        assert d.leb() == 0 and d.byte() == 0x41
        address = d.leb(True)
        assert address >= 0 and d.byte() == 0x0b
        payload = list(d.take(d.leb()))
        assert address + len(payload) <= 131072
        data.append((address,payload))
    d.done()
    lines = ['import Proofs.Wasm', '', 'namespace Artifact',
             f'def localCount : Nat := {len(locals_)}',
             'def data : List (Nat × List Nat) := [' + ', '.join(f'({a},{bs})' for a,bs in data) + ']',
             'def code (pc : Nat) : Option Wasm.Instr :=']
    def table(lo, hi):
        if hi-lo == 1:
            name, *args = ops[lo]
            args = ['.' + x if isinstance(x,str) else str(x) for x in args]
            ins = '.' + name + (' ' + ' '.join(args) if args else '')
            return f'(if pc = {lo} then some ({ins}) else none)'
        mid = (lo+hi)//2
        return f'(if pc < {mid} then\n{table(lo,mid)}\nelse {table(mid,hi)})'
    lines += [table(0,len(ops)), 'end Artifact', '']
    return '\n'.join(lines), ops, len(locals_)

if __name__ == '__main__':
    import sys
    generated, ops, n = extract()
    target = ROOT / 'Proofs/Artifact.lean'
    if '--check' in sys.argv:
        assert target.read_text() == generated, 'artifact extraction differs'
    else:
        target.write_text(generated)
    print(f'artifact SHA256 {SHA}; {len(ops)} instructions, {n} locals')
