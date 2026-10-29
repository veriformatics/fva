#!/usr/bin/env python3
"""Supplementary Wasmtime tests, not proofs. Uses the original binary verbatim."""
import hashlib
import pathlib
import random
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
ARTIFACT_SHA256 = "1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775"


def decode(data):
    """Independent sequence decoder. Deliberately does not enforce end conditions."""
    pos = 0
    out = bytearray()

    def take():
        nonlocal pos
        if pos == len(data):
            raise ValueError("truncated field")
        b = data[pos]
        pos += 1
        return b

    def length(base):
        if base == 15:
            while True:
                b = take()
                base += b
                if b != 255:
                    break
        return base

    try:
        while True:
            token = take()
            count = length(token >> 4)
            if pos + count > len(data):
                raise ValueError("truncated literals")
            out.extend(data[pos:pos + count])
            pos += count
            if pos == len(data):
                return bytes(out)
            offset = take() + 256 * take()
            if not 1 <= offset <= len(out):
                raise ValueError("independent-block offset")
            count = 4 + length(token & 15)
            for _ in range(count):
                out.append(out[-offset])
    except ValueError:
        return None


def extension(n):
    return bytes([255] * (n // 255) + [n % 255])


def literals(bs):
    return bytes([min(15, len(bs)) << 4]) + (
        extension(len(bs) - 15) if len(bs) >= 15 else b"") + bs


def cases():
    # These 17 inputs/capacities mirror the finite Lean Sample claims.
    fixed = [
        (b"\x00", 0), (b"\x50hello", 5),
        (b"\xf0\x00" + bytes(range(15)), 15),
        (bytes([19, 65, 1, 0, 80, 66, 67, 68, 69, 70]), 13),
        (bytes([35, 65, 66, 2, 0, 80, 67, 68, 69, 70, 71]), 14),
        (bytes([31, 65, 1, 0, 0, 80, 66, 67, 68, 69, 70]), 25),
        (bytes([16, 65, 1, 0, 240, 20]) + b"B" * 35, 40),
        (bytes([64, 65, 66, 67, 68, 4, 0, 240, 20]) + b"E" * 35, 64),
        (b"\xf0", 32), (bytes([16, 65, 0, 0]), 32), (bytes([0, 1, 0]), 32),
        (bytes([32, 65]), 32), (bytes([0, 1]), 32), (b"\x50hello", 4),
        (bytes([16, 65, 1, 0, 0]), 5),
        (bytes([240, 17]) + bytes(range(32)) + bytes([32, 0, 240, 20]) + b"E" * 35, 71),
        (bytes([255, 49]) + bytes(range(64)) + bytes([64, 0, 14, 240, 20]) + b"E" * 35, 132),
    ]
    for data, cap in fixed:
        yield data, cap, True, 0
    rng = random.Random(0x4C5A34)
    for n in list(range(41)) + [63, 64, 65, 255, 269, 270, 271, 511]:
        data = literals(rng.randbytes(n))
        yield data, n, True, 165
    for _ in range(180):
        head = rng.randbytes(rng.randint(1, 80))
        offset = rng.randint(1, len(head))
        match = rng.randint(4, 100)
        tail = rng.randbytes(rng.randint(8, 40))
        token = min(15, len(head)) * 16 + min(15, match - 4)
        data = bytes([token]) + (extension(len(head) - 15) if len(head) >= 15 else b"")
        data += head + offset.to_bytes(2, "little")
        data += extension(match - 19) if match >= 19 else b""
        data += literals(tail)
        size = len(head) + match + len(tail)
        yield data, size + rng.choice([0, 1, 31, 64]), True, 165
        yield data, rng.randrange(size), True, 165
    for _ in range(200):
        yield rng.randbytes(rng.randrange(40)), rng.randrange(512), False, 165


def escaped(bs):
    return '"' + ''.join(f"\\{b:02x}" for b in bs) + '"'


def wast(binary, samples):
    text = [f"(module $subject binary {escaped(binary)})", '(register "subject" $subject)']
    for i, (data, cap, required, fill) in enumerate(samples):
        src, dst = (131072, 262144) if i % 2 == 0 else (524288, 131072)
        out = decode(data)
        expected = -1 if out is None or len(out) > cap else len(out)
        # Relaxed-format blocks may be rejected. Valid generated blocks must succeed.
        optional = expected >= 0 and not required
        text += ['(module', ' (import "subject" "memory" (memory 32 32))',
                 ' (import "subject" "lz4_decompress" (func $decode (param i32 i32 i32 i32) (result i32)))',
                 f' (data (i32.const {src}) {escaped(data)})',
                 ' (func (export "test") (result i32) (local $r i32)',
                 f'  (memory.fill (i32.const {dst - 16}) (i32.const {fill}) (i32.const {cap + 32}))',
                 f'  (local.set $r (call $decode (i32.const {src}) (i32.const {dst}) '
                 f'(i32.const {len(data)}) (i32.const {cap})))']

        def check(expr):
            text.append(f'  (if (i32.eqz {expr}) (then unreachable))')

        for k in list(range(-16, 0)) + list(range(cap, cap + 16)):
            check(f'(i32.eq (i32.load8_u (i32.const {dst + k})) (i32.const {fill}))')
        for k, byte in enumerate(data):
            check(f'(i32.eq (i32.load8_u (i32.const {src + k})) (i32.const {byte}))')
        if optional:
            text.append('  (if (i32.eq (local.get $r) (i32.const -1)) (then (return (i32.const 1))))')
        check(f'(i32.eq (local.get $r) (i32.const {expected}))')
        if expected >= 0:
            for k, byte in enumerate(out):
                check(f'(i32.eq (i32.load8_u (i32.const {dst + k})) (i32.const {byte}))')
        text += ['  (i32.const 1)))', '(assert_return (invoke "test") (i32.const 1))']
    return '\n'.join(text) + '\n'


def main():
    binary = (ROOT / "lz4-flex.wasm").read_bytes()
    assert len(binary) == 7161 and hashlib.sha256(binary).hexdigest() == ARTIFACT_SHA256
    samples = list(cases())
    with tempfile.TemporaryDirectory(prefix="lz4-runtime-") as tmp:
        script = pathlib.Path(tmp) / "checks.wast"
        script.write_text(wast(binary, samples))
        subprocess.run(["wasmtime", "wast", "-C", "cache=n", str(script)], check=True)
    print(f"PASS: {len(samples)} Wasmtime cases; exact artifact, return/output/source/guard checks")


if __name__ == "__main__":
    main()
