"""Toy compiler (an untrusted producer): an arithmetic expression over x, fully parenthesized,
to a WebAssembly module exporting f(x: i32) -> i32. Usage: compile.py < expr.txt > out.wasm"""

import sys


def uleb(n):
    out = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        out.append(b | (0x80 if n else 0))
        if not n:
            return bytes(out)


def sleb(n):
    out = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        done = (n == 0 and not b & 0x40) or (n == -1 and b & 0x40)
        out.append(b | (0 if done else 0x80))
        if done:
            return bytes(out)


def parse(s, i):
    if s[i] == "x":
        return ("x",), i + 1
    if s[i] == "(":
        a, i = parse(s, i + 1)
        op = s[i]
        b, i = parse(s, i + 1)
        assert s[i] == ")"
        return (op, a, b), i + 1
    j = i
    while j < len(s) and s[j].isdigit():
        j += 1
    return ("const", int(s[i:j])), j


def emit(e):
    if e[0] == "x":
        return b"\x20\x00"
    if e[0] == "const":
        v = e[1] % 2**32
        return b"\x41" + sleb(v - 2**32 if v >= 2**31 else v)
    return emit(e[1]) + emit(e[2]) + {"+": b"\x6a", "-": b"\x6b", "*": b"\x6c"}[e[0]]


def section(n, body):
    return bytes([n]) + uleb(len(body)) + body


src = sys.stdin.read().strip()
e, end = parse(src, 0)
assert end == len(src)
code = b"\x00" + emit(e) + b"\x0b"
sys.stdout.buffer.write(
    b"\x00asm\x01\x00\x00\x00"
    + section(1, b"\x01\x60\x01\x7f\x01\x7f")
    + section(3, b"\x01\x00")
    + section(7, b"\x01\x01f\x00\x00")
    + section(10, b"\x01" + uleb(len(code)) + code)
)
