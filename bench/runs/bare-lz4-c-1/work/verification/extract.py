#!/usr/bin/env python3
"""Decode the pinned Wasm bytes, resolve void control labels, emit Lean data.
No C compilation or hand transcription is used. --check compares the output.
Only the actual instruction subset is supported; all other opcodes are errors.
"""
import argparse
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SHA = "8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6"


class Reader:
    def __init__(self, data):
        self.data, self.pos = data, 0

    def byte(self):
        b = self.data[self.pos]
        self.pos += 1
        return b

    def take(self, n):
        assert self.pos + n <= len(self.data)
        b = self.data[self.pos:self.pos + n]
        self.pos += n
        return b

    def leb(self, signed=False):
        n = shift = 0
        while True:
            b = self.byte()
            n |= (b & 127) << shift
            shift += 7
            assert shift <= 35
            if not b & 128:
                return n - (1 << shift) if signed and b & 64 else n

    def name(self):
        return self.take(self.leb()).decode()

    def done(self):
        assert self.pos == len(self.data)


def module():
    raw = (ROOT / "lz4-c.wasm").read_bytes()
    assert len(raw) == 8469 and hashlib.sha256(raw).hexdigest() == SHA
    r = Reader(raw)
    assert r.take(8) == b"\0asm\x01\0\0\0"
    sections = {}
    while r.pos < len(raw):
        section = r.byte()
        assert section not in sections and section != 0
        sections[section] = r.take(r.leb())
    assert 2 not in sections and 8 not in sections  # no imports or start
    r = Reader(sections[1])
    types = []
    for _ in range(r.leb()):
        assert r.byte() == 0x60
        args = [r.byte() for _ in range(r.leb())]
        results = [r.byte() for _ in range(r.leb())]
        assert set(args) == {0x7f} and results == [0x7f]
        types.append(len(args))
    r.done()
    r = Reader(sections[3])
    signatures = [types[r.leb()] for _ in range(r.leb())]
    r.done()
    r = Reader(sections[5])
    assert [r.leb() for _ in range(4)] == [1, 1, 32, 32]
    r.done()
    r = Reader(sections[7])
    exports = {r.name(): (r.byte(), r.leb()) for _ in range(r.leb())}
    r.done()
    assert exports == {"memory": (2, 0), "LZ4_compress_default": (0, 1),
                       "LZ4_decompress_safe": (0, 2)}
    r = Reader(sections[10])
    bodies = [r.take(r.leb()) for _ in range(r.leb())]
    r.done()
    assert len(bodies) == len(signatures) == 6
    r = Reader(sections[11])
    assert r.leb() == 1 and r.leb() == 0 and r.byte() == 0x41
    data_address = r.leb(True)
    assert data_address == 65536 and r.byte() == 0x0b
    data = r.take(r.leb())
    r.done()
    assert len(data) == 64
    return raw, signatures, bodies, data


BIN = {0x6a: "add", 0x6b: "sub", 0x71: "and", 0x73: "xor", 0x74: "shl",
       0x76: "shr", 0x46: "eq", 0x47: "ne", 0x49: "ltu", 0x4d: "leu",
       0x4b: "gtu", 0x4f: "geu", 0x48: "lts"}
MEM = {0x28: ("load", 4), 0x2d: ("load", 1), 0x2f: ("load", 2),
       0x36: ("store", 4), 0x3a: ("store", 1)}


def decode(body, params, signatures):
    r = Reader(body)
    locals_count = 0
    for _ in range(r.leb()):
        locals_count += r.leb()
        assert r.byte() == 0x7f
    code, labels = [], []
    height = 0
    while True:
        op = r.byte()
        if op in (2, 3):
            assert r.byte() == 0x40  # no block parameters/results
            assert height == 0  # all branch targets have empty operand stacks
            labels.append({"loop": op == 3, "start": len(code), "fix": []})
            continue
        if op == 0x0b:
            if not labels:
                assert height in (None, 1)
                code.append(".ret")
                break
            assert height in (None, 0)
            label = labels.pop()
            target = label["start"] if label["loop"] else len(code)
            for idx, kind in label["fix"]:
                code[idx] = f".{kind} {target}"
            height = 0
            continue
        if op in (0x0c, 0x0d):
            depth = r.leb()
            assert depth < len(labels)
            if height is not None:
                height -= op == 0x0d
                assert height == 0
            label = labels[-depth - 1]
            label["fix"].append((len(code), "jumpIf" if op == 0x0d else "jump"))
            code.append(None)
            if op == 0x0c:
                height = None
            continue
        delta = 0
        if op == 0x41:
            ins, delta = f".const {r.leb(True) % (1 << 32)}", 1
        elif op in (0x20, 0x21, 0x22):
            i = r.leb()
            assert i < params + locals_count
            ins = f".{ {0x20: 'get', 0x21: 'set', 0x22: 'tee'}[op]} {i}"
            delta = {0x20: 1, 0x21: -1, 0x22: 0}[op]
        elif op in BIN:
            ins, delta = f".bin .{BIN[op]}", -1
        elif op == 0x45:
            ins = ".eqz"
        elif op in MEM:
            kind, width = MEM[op]
            align, offset = r.leb(), r.leb()
            assert (1 << align) <= width
            ins = f".{kind} {width} {offset}"
            delta = -2 if kind == "store" else 0
        elif op == 0x10:
            callee = r.leb()
            assert callee in (3, 4)
            ins, delta = f".call {callee}", 1 - signatures[callee]
        elif op == 0x1a:
            ins, delta = ".drop", -1
        elif op == 0x1b:
            ins, delta = ".select", -2
        elif op == 0x0f:
            assert height == 1
            ins, height = ".ret", None
        else:
            raise AssertionError(f"unsupported opcode {op:#x}")
        if height is not None:
            height += delta
            assert height >= 0
        code.append(ins)
    r.done()
    assert all(i is not None for i in code)
    return locals_count, code


def generated():
    _, signatures, bodies, data = module()
    out = ["-- Generated by verification/extract.py from the pinned binary. Do not edit.",
           "import Proofs.Wasm", "set_option maxRecDepth 10000", "namespace Artifact", "open Wasm", f'def sha256 : String := "{SHA}"']
    for i in (2, 3, 4):
        locals_count, code = decode(bodies[i], signatures[i], signatures)
        chunks = [code[j:j + 16] for j in range(0, len(code), 16)]
        for j, chunk in enumerate(chunks):
            out += [f"def chunk{i}_{j} : Array Instr := #[" + ", ".join(chunk) + "]"]
        out += [f"def func{i} : Func := ⟨{signatures[i]}, {locals_count}, fun pc =>",
                "  match pc / 16 with",
                "\n".join(f"  | {j} => chunk{i}_{j}[pc % 16]?" for j in range(len(chunks))),
                "  | _ => none⟩"]
    out += ["def program : Nat → Func", "  | 2 => func2", "  | 3 => func3",
            "  | 4 => func4", "  | _ => ⟨0, 0, fun _ => none⟩"]
    out += ["def staticData : List Nat := [" + ", ".join(map(str, data)) + "]"]
    out += ["end Artifact", ""]
    return "\n".join(out)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    target = ROOT / "Proofs" / "Artifact.lean"
    content = generated()
    if args.check:
        assert target.read_text() == content, "regenerate Artifact.lean"
        print("PASS: pinned binary, interface, and exact generated Lean instruction data")
    else:
        target.write_text(content)
        print("Generated Proofs/Artifact.lean")
