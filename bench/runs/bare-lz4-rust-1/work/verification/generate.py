#!/usr/bin/env python3
"""Bind the verification model to the immutable shipped bytes. No build of Rust.

The Lean theorem additionally checks instruction decoding from the extracted body.
The module-section extraction and structural assertions below are trusted glue.
"""
import argparse
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXPECTED = "1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775"


class Reader:
    def __init__(self, data):
        self.data, self.pos = data, 0

    def byte(self):
        assert self.pos < len(self.data), "unexpected end of binary"
        v = self.data[self.pos]
        self.pos += 1
        return v

    def take(self, n):
        assert self.pos + n <= len(self.data)
        v = self.data[self.pos:self.pos+n]
        self.pos += n
        return v

    def uleb(self):
        v = shift = 0
        while True:
            b = self.byte()
            v |= (b & 127) << shift
            if b < 128:
                return v
            shift += 7
            assert shift < 35

    def sleb(self):
        v = shift = 0
        while True:
            b = self.byte()
            v |= (b & 127) << shift
            shift += 7
            if b < 128:
                return v - (1 << shift) if b & 64 else v
            assert shift < 35

    def name(self):
        return self.take(self.uleb()).decode("utf-8")

    def done(self):
        assert self.pos == len(self.data), "unconsumed bytes"


def extract(data):
    r = Reader(data)
    assert r.take(8) == b"\0asm\x01\0\0\0"
    sections = {}
    while r.pos < len(data):
        tag = r.byte()
        payload = r.take(r.uleb())
        assert tag and tag not in sections
        sections[tag] = payload
    assert set(sections) == {1, 3, 5, 6, 7, 10, 11}
    r = Reader(sections[1])
    types = []
    for _ in range(r.uleb()):
        assert r.byte() == 0x60
        args = r.take(r.uleb())
        rets = r.take(r.uleb())
        types.append((args, rets))
    r.done()
    r = Reader(sections[3])
    functypes = [r.uleb() for _ in range(r.uleb())]
    r.done()
    assert len(functypes) == 9
    assert types[functypes[7]] == (bytes([127]*4), bytes([127]))
    r = Reader(sections[5])
    assert [r.uleb() for _ in range(4)] == [1, 1, 32, 32]
    r.done()
    r = Reader(sections[7])
    exports = {}
    for _ in range(r.uleb()):
        name = r.name()
        exports[name] = (r.byte(), r.uleb())
    r.done()
    assert exports == {"memory": (2, 0), "lz4_compress": (0, 6),
                       "lz4_decompress": (0, 7)}
    r = Reader(sections[10])
    bodies = [r.take(r.uleb()) for _ in range(r.uleb())]
    r.done()
    assert len(bodies) == 9
    r = Reader(sections[11])
    assert r.uleb() == 1 and r.uleb() == 0 and r.byte() == 0x41
    address = r.sleb()
    assert r.byte() == 0x0b
    segment = r.take(r.uleb())
    r.done()
    assert address == 65536 and address + len(segment) < 131072
    return bodies[7], address, segment


def instructions(body):
    r = Reader(body)
    locals_count = 0
    for _ in range(r.uleb()):
        locals_count += r.uleb()
        assert r.byte() in (0x7f, 0x7e)
    code, blocks = [], []
    names = {0x00: "unreachable", 0x0b: "end", 0x0f: "ret", 0x1b: "select",
             0x45: "eqz", 0x46: "eq", 0x47: "ne", 0x49: "lt", 0x4b: "gt",
             0x4d: "le", 0x4f: "ge", 0x6a: "add", 0x6b: "sub",
             0x71: "band", 0x76: "shr"}
    while r.pos < len(body):
        op = r.byte()
        if op in (0x02, 0x03):
            assert r.byte() == 0x40
            blocks.append(len(code))
            item = ("block" if op == 2 else "loop", 0)
        elif op == 0x0b:
            if blocks:
                start = blocks.pop()
                code[start] = (code[start][0], len(code))
            else:
                assert r.pos == len(body)
            item = ("end",)
        elif op in (0x0c, 0x0d, 0x20, 0x21, 0x22):
            item = ({0x0c: "br", 0x0d: "brIf", 0x20: "get", 0x21: "set",
                     0x22: "tee"}[op], r.uleb())
        elif op == 0x10:
            r.uleb()
            item = ("unsupported", op)
        elif op == 0x41:
            item = ("const", r.sleb() % (1 << 32))
        elif op in (0x28, 0x29, 0x2d, 0x2f, 0x36, 0x37, 0x3a, 0x3b):
            r.uleb()  # Alignment hint, no effect on Wasm semantics.
            width = {0x28: 4, 0x29: 8, 0x2d: 1, 0x2f: 2,
                     0x36: 4, 0x37: 8, 0x3a: 1, 0x3b: 2}[op]
            item = ("load" if op < 0x36 else "store", width, r.uleb())
        elif op == 0xfc:
            sub = r.uleb()
            assert sub in (10, 11) and r.byte() == 0
            if sub == 10:
                assert r.byte() == 0
            item = ("copy" if sub == 10 else "fill",)
        elif op in names:
            item = (names[op],)
        else:
            raise AssertionError(f"unsupported opcode {op:#x}")
        code.append(item)
    assert not blocks
    return locals_count, code


def nums(xs):
    return "[" + ", ".join(map(str, xs)) + "]"


def generated(data):
    body, address, segment = extract(data)
    nlocals, code = instructions(body)
    ops = ",\n  ".join("." + " ".join(map(str, op)) for op in code)
    return f'''-- Generated by verification/generate.py from lz4-flex.wasm; do not edit.
import Proofs.DecodeWasm
namespace Artifact
def sha256 : String := "{EXPECTED}"
def body : List Nat := {nums(body)}
def dataAddress : Nat := {address}
def dataBytes : List Nat := {nums(segment)}
def localCount : Nat := {nlocals}
def code : Array Wasm.Op := #[
  {ops}]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem instruction_decode : Wasm.decodeBody body = some (localCount, code) := by
  native_decide
end Artifact
'''


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--check", action="store_true")
    args = p.parse_args()
    data = (ROOT / "lz4-flex.wasm").read_bytes()
    assert len(data) == 7161 and hashlib.sha256(data).hexdigest() == EXPECTED
    result = generated(data)
    path = ROOT / "Proofs/Artifact.lean"
    if args.check:
        assert path.read_text() == result, "generated Lean model differs"
    else:
        path.write_text(result)
    print("PASS: artifact SHA-256, module structure, and generated decoder model")


if __name__ == "__main__":
    main()
