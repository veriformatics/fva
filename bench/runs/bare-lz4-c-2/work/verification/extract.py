#!/usr/bin/env python3
"""Strict decoder for the exact shipped Wasm; emit the reachable Lean program.

No compiler or source C is involved. --check compares regenerated text to the
checked-in file. Unsupported binary constructs raise an error.
"""
from pathlib import Path
import argparse
import hashlib

ROOT = Path(__file__).resolve().parent.parent
SHA256 = "8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6"


class Reader:
    def __init__(self, data):
        self.data, self.pos = data, 0

    def take(self, n):
        assert self.pos + n <= len(self.data), "truncated binary"
        result = self.data[self.pos:self.pos + n]
        self.pos += n
        return result

    def byte(self):
        return self.take(1)[0]

    def leb(self, signed=False):
        n, shift = 0, 0
        while True:
            b = self.byte()
            n |= (b & 127) << shift
            shift += 7
            assert shift <= 35
            if not b & 128:
                if signed and b & 64:
                    n -= 1 << shift
                return n

    def vector(self, f):
        return [f() for _ in range(self.leb())]

    def name(self):
        return self.take(self.leb()).decode("utf8")

    def done(self):
        assert self.pos == len(self.data), "unconsumed bytes"


BIN = {0x6A: "add", 0x6B: "sub", 0x71: "band", 0x73: "bxor",
       0x74: "shl", 0x76: "shr", 0x46: "eq", 0x47: "ne",
       0x49: "ltu", 0x4D: "leu", 0x4B: "gtu", 0x4F: "geu", 0x48: "lts"}


def decode(body):
    r = Reader(body)
    locals_count = 0
    for _ in range(r.leb()):
        n, ty = r.leb(), r.byte()
        assert ty == 0x7F
        locals_count += n
    code, blocks, calls = [], [], set()
    while r.pos < len(r.data):
        op = r.byte()
        if op in (0x02, 0x03):
            assert r.byte() == 0x40, "only empty block types supported"
            blocks.append(len(code))
            ins = ["block", None, op == 0x03]
        elif op == 0x0B:
            if blocks:
                code[blocks.pop()][1] = len(code)
                ins = ["end"]
            else:
                ins = ["ret"]
                assert r.pos == len(r.data)
        elif op in (0x0C, 0x0D):
            depth = r.leb()
            assert depth < len(blocks), "function-label branches unsupported"
            ins = ["br" if op == 0x0C else "brIf", depth]
        elif op == 0x0F:
            ins = ["ret"]
        elif op == 0x10:
            fn = r.leb()
            calls.add(fn)
            ins = ["call", fn]
        elif op in (0x1A, 0x1B, 0x45):
            ins = [{0x1A: "drop", 0x1B: "select", 0x45: "eqz"}[op]]
        elif op in (0x20, 0x21, 0x22):
            ins = [{0x20: "get", 0x21: "set", 0x22: "tee"}[op], r.leb()]
        elif op in (0x28, 0x2D, 0x2F, 0x36, 0x3A):
            alignment, offset = r.leb(), r.leb()
            width = {0x28: 4, 0x2D: 1, 0x2F: 2, 0x36: 4, 0x3A: 1}[op]
            assert 1 << alignment <= width
            ins = ["store" if op in (0x36, 0x3A) else "load", width, offset]
        elif op == 0x41:
            value = r.leb(signed=True)
            assert -(1 << 31) <= value < (1 << 31)
            ins = ["const", value % (1 << 32)]
        elif op in BIN:
            ins = ["bin", "." + BIN[op]]
        else:
            raise ValueError(f"unsupported reachable opcode {op:#x}")
        code.append(ins)
    assert not blocks
    r.done()
    return locals_count, code, calls


def extract():
    artifact = (ROOT / "lz4-c.wasm").read_bytes()
    assert len(artifact) == 8469
    assert hashlib.sha256(artifact).hexdigest() == SHA256
    r = Reader(artifact)
    assert r.take(8) == b"\0asm\x01\0\0\0"
    sections = {}
    while r.pos < len(r.data):
        kind = r.byte()
        assert kind not in sections and kind in (1, 3, 5, 6, 7, 10, 11)
        sections[kind] = Reader(r.take(r.leb()))
    assert set(sections) == {1, 3, 5, 6, 7, 10, 11}
    s = sections[1]
    types = []
    for _ in range(s.leb()):
        assert s.byte() == 0x60
        params = s.vector(s.byte)
        results = s.vector(s.byte)
        assert all(t == 0x7F for t in params) and results == [0x7F]
        types.append(len(params))
    s.done()
    s = sections[3]
    function_types = s.vector(s.leb)
    s.done()
    assert function_types == [0, 1, 1, 2, 2, 2]
    assert types == [6, 4, 3]
    s = sections[5]
    assert s.leb() == 1 and s.byte() == 1 and s.leb() == 32 and s.leb() == 32
    s.done()
    s = sections[6]
    assert s.leb() == 1 and s.byte() == 0x7F and s.byte() == 1
    assert s.byte() == 0x41 and s.leb(True) == 65536 and s.byte() == 0x0B
    s.done()
    s = sections[7]
    exports = [(s.name(), s.byte(), s.leb()) for _ in range(s.leb())]
    assert exports == [("memory", 2, 0), ("LZ4_compress_default", 0, 1),
                       ("LZ4_decompress_safe", 0, 2)]
    s.done()
    s = sections[10]
    bodies = [s.take(s.leb()) for _ in range(s.leb())]
    s.done()
    assert len(bodies) == 6
    s = sections[11]
    assert s.leb() == 1 and s.leb() == 0 and s.byte() == 0x41
    address = s.leb(True)
    assert address == 65536 and s.byte() == 0x0B
    data = s.take(s.leb())
    s.done()
    decoded, pending = {}, [2]
    while pending:
        fn = pending.pop()
        if fn in decoded:
            continue
        decoded[fn] = decode(bodies[fn])
        pending.extend(decoded[fn][2])
    assert set(decoded) == {2, 3, 4}
    out = ["-- Generated from the exact binary by verification/extract.py; do not edit.",
           f"-- SHA-256: {SHA256}", "import Proofs.Wasm", "namespace Verification.Artifact",
           "open Wasm", "def program : Array Func := #["]
    for fn in range(6):
        if fn not in decoded:
            out.append("  ⟨0, 0, #[]⟩, -- unreachable function " + str(fn))
            continue
        locals_count, code, _ = decoded[fn]
        out.append(f"  ⟨{types[function_types[fn]]}, {locals_count}, #[ -- function {fn}")
        for ins in code:
            args = " ".join(str(a).lower() if isinstance(a, bool) else str(a) for a in ins[1:])
            out.append("    ." + ins[0] + (" " + args if args else "") + ",")
        out.append("  ]⟩,")
    out += ["]", "def initialData : Memory := putBytes [] 65536 [" +
            ", ".join(map(str, data)) + "]", "end Verification.Artifact", ""]
    return "\n".join(out)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    output = extract()
    target = ROOT / "Proofs/Artifact.lean"
    if args.check:
        assert target.read_text() == output, "generated Lean program differs"
        print("PASS: exact artifact digest, interface, reachable code and data")
    else:
        target.write_text(output)
        print("Wrote Proofs/Artifact.lean")
