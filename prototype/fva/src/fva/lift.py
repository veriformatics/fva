"""wasm binary → Lean `FVA.Wasm.Module` value. Decodes exactly the subset the Lean
semantics models; any other opcode = hard error naming it (never silently skipped)."""

import hashlib
import re
from dataclasses import dataclass, field

VALTYPE = {0x7F: "i32", 0x7E: "i64"}
SIMPLE = {0x00: ".unreachable", 0x01: ".nop", 0x0F: ".ret", 0x1A: ".drop", 0x1B: ".select",
          0x45: ".i32Eqz", 0x50: ".i64Eqz", 0xA7: ".i32WrapI64",
          0xAC: ".i64ExtendI32S", 0xAD: ".i64ExtendI32U"}
REL = ["eq", "ne", "ltS", "ltU", "gtS", "gtU", "leS", "leU", "geS", "geU"]
BIN = ["add", "sub", "mul", "divS", "divU", "remS", "remU", "and", "or", "xor", "shl", "shrS", "shrU"]
for k, op in enumerate(REL):
    SIMPLE[0x46 + k] = f"(.i32Rel .{op})"
    SIMPLE[0x51 + k] = f"(.i64Rel .{op})"
for k, op in enumerate(BIN):
    SIMPLE[0x6A + k] = f"(.i32Bin .{op})"
    SIMPLE[0x7C + k] = f"(.i64Bin .{op})"


class LiftError(Exception):
    pass


class Reader:
    def __init__(self, b: bytes, pos: int = 0, end: int | None = None):
        self.b, self.pos, self.end = b, pos, len(b) if end is None else end

    def byte(self) -> int:
        if self.pos >= self.end:
            raise LiftError("unexpected end of input")
        v = self.b[self.pos]
        self.pos += 1
        return v

    def uleb(self) -> int:
        r = shift = 0
        while True:
            v = self.byte()
            r |= (v & 0x7F) << shift
            shift += 7
            if not v & 0x80:
                return r

    def sleb(self, bits: int) -> int:
        r = shift = 0
        while True:
            v = self.byte()
            r |= (v & 0x7F) << shift
            shift += 7
            if not v & 0x80:
                if v & 0x40:
                    r -= 1 << shift
                return r & ((1 << bits) - 1)

    def name(self) -> str:
        n = self.uleb()
        s = self.b[self.pos:self.pos + n].decode()
        self.pos += n
        return s

    def done(self) -> bool:
        return self.pos >= self.end


@dataclass
class Func:
    name: str
    params: list[str]
    results: int
    locals: list[str] = field(default_factory=list)
    body: str = ""


def block_arity(r: Reader) -> int:
    bt = r.byte()
    if bt == 0x40:
        return 0
    if bt in VALTYPE:
        return 1
    raise LiftError(f"block type 0x{bt:02x} (type-indexed blocks) unsupported")


def instrs(r: Reader, indent: int) -> tuple[str, int]:
    """Decode until `end`/`else`; returns (Lean list literal, terminating opcode)."""
    out = []
    pad = "  " * indent
    while True:
        op = r.byte()
        if op in (0x0B, 0x05):
            body = ("[\n" + ",\n".join(pad + "  " + i for i in out) + "]") if out else "[]"
            return body, op
        if op in SIMPLE:
            out.append(SIMPLE[op])
        elif op in (0x20, 0x21, 0x22):
            out.append(f"(.{['localGet', 'localSet', 'localTee'][op - 0x20]} {r.uleb()})")
        elif op in (0x0C, 0x0D):
            out.append(f"(.{'br' if op == 0x0C else 'brIf'} {r.uleb()})")
        elif op == 0x41:
            out.append(f"(.i32Const {r.sleb(32)}#32)")
        elif op == 0x42:
            out.append(f"(.i64Const {r.sleb(64)}#64)")
        elif op in (0x02, 0x03):
            n = block_arity(r)
            body, _ = instrs(r, indent + 1)
            out.append(f"(.{'block' if op == 0x02 else 'loop'} {n} {body})")
        elif op == 0x04:
            n = block_arity(r)
            thn, term = instrs(r, indent + 1)
            els = instrs(r, indent + 1)[0] if term == 0x05 else "[]"
            out.append(f"(.ite {n} {thn} {els})")
        else:
            raise LiftError(f"opcode 0x{op:02x} at byte {r.pos - 1} outside FVA's modeled subset")


def decode(wasm: bytes) -> list[Func]:
    if wasm[:8] != b"\0asm\1\0\0\0":
        raise LiftError("not a wasm v1 binary")
    r = Reader(wasm, 8)
    types, fn_types, exports, bodies = [], [], {}, []
    while not r.done():
        sid, size = r.byte(), r.uleb()
        s = Reader(wasm, r.pos, r.pos + size)
        r.pos += size
        if sid == 1:
            for _ in range(s.uleb()):
                if s.byte() != 0x60:
                    raise LiftError("malformed func type")
                params = [VALTYPE[s.byte()] for _ in range(s.uleb())]
                results = [VALTYPE[s.byte()] for _ in range(s.uleb())]
                types.append((params, len(results)))
        elif sid == 2 and s.uleb():
            raise LiftError("imports unsupported (index space would shift)")
        elif sid == 3:
            fn_types = [s.uleb() for _ in range(s.uleb())]
        elif sid == 7:
            for _ in range(s.uleb()):
                name, kind, idx = s.name(), s.byte(), s.uleb()
                if kind == 0:
                    exports[idx] = name
        elif sid == 10:
            for _ in range(s.uleb()):
                size = s.uleb()
                bodies.append((s.pos, s.pos + size))
                s.pos += size
    funcs = []
    for idx, name in sorted(exports.items()):
        params, results = types[fn_types[idx]]
        start, end = bodies[idx]
        c = Reader(wasm, start, end)
        locs = []
        for _ in range(c.uleb()):
            n, t = c.uleb(), c.byte()
            locs += [VALTYPE[t]] * n
        body, _ = instrs(c, 1)
        funcs.append(Func(name, params, results, locs, body))
    return funcs


def ident(name: str) -> str:
    s = re.sub(r"\W", "_", name)
    return f"«{s}»" if s[0].isdigit() else s


def to_lean(wasm: bytes, ns: str, src: str) -> str:
    sha = hashlib.sha256(wasm).hexdigest()
    funcs = decode(wasm)
    ty = lambda ts: "[" + ", ".join("." + t for t in ts) + "]"
    parts = [
        "import FVA.Wasm.Semantics\n",
        f"/-! Generated by `fva lift` from `{src}` — do not edit; regenerate.\n"
        f"Proofs about `module` are proofs about exactly these bytes. -/\n",
        f"namespace {ns}\nopen FVA.Wasm\n",
        f'def wasmSha256 : String := "{sha}"\n',
    ]
    for f in funcs:
        parts.append(
            f"def {ident(f.name)} : Func where\n"
            f'  name := "{f.name}"\n  params := {ty(f.params)}\n  locals := {ty(f.locals)}\n'
            f"  results := {f.results}\n  body := {f.body}\n")
    parts.append(f"def module : Module where\n  funcs := [{', '.join(ident(f.name) for f in funcs)}]\n")
    parts.append(f"end {ns}\n")
    return "\n".join(parts)
