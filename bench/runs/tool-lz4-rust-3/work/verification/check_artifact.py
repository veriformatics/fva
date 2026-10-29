#!/usr/bin/env python3
"""Finite checks of the *original* module using a separate importing WASM harness.

This is testing, not a universal proof or a verified translator. No dependencies
beyond Python's standard library, wasm-tools, and wasmtime are used.
"""
import hashlib
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
EXPECTED = "1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775"


def extension(n):
    return bytes([255]) * (n // 255) + bytes([n % 255])


def literal(data):
    n = len(data)
    return bytes([min(n, 15) << 4]) + (extension(n - 15) if n >= 15 else b"") + data


def match(lits, offset, count):
    assert count >= 4 and 1 <= offset <= len(lits)
    return (bytes([(min(len(lits), 15) << 4) | min(count - 4, 15)])
            + (extension(len(lits) - 15) if len(lits) >= 15 else b"")
            + lits + offset.to_bytes(2, "little")
            + (extension(count - 19) if count >= 19 else b""))


def oracle(data, cap):
    """Direct byte parser; only compare returned prefix on success.

    Accepts relaxed end conditions as R3 permits. Returning -1 is expected on
    the hand-built malformed cases; README R3 alone does not require rejection
    of every malformed block.
    """
    ip, out = 0, bytearray()

    def field(n):
        nonlocal ip
        if n == 15:
            while True:
                if ip == len(data):
                    raise ValueError("truncated length")
                b = data[ip]
                ip += 1
                n += b
                if b != 255:
                    break
        return n

    try:
        while True:
            if ip == len(data):
                raise ValueError("missing token")
            token = data[ip]
            ip += 1
            ll = field(token >> 4)
            if ll > len(data) - ip or ll > cap - len(out):
                raise ValueError("literal exceeds buffer")
            out.extend(data[ip:ip + ll])
            ip += ll
            if ip == len(data):
                return len(out), bytes(out)
            if len(data) - ip < 2:
                raise ValueError("truncated offset")
            off = int.from_bytes(data[ip:ip + 2], "little")
            ip += 2
            ml = field(token & 15) + 4
            if not 1 <= off <= len(out) or ml > cap - len(out):
                raise ValueError("invalid match")
            for _ in range(ml):
                out.append(out[-off])
    except ValueError:
        return -1, b""


def cases():
    result = []

    def add(name, data, cap):
        r, out = oracle(data, cap)
        result.append((name, data, cap, r, out))

    for n in [0, 1, 2, 3, 4, 5, 7, 8, 14, 15, 16, 17, 31, 32, 33, 254, 255, 269, 270, 1024]:
        data = literal(bytes((i * 17 + 3) % 256 for i in range(n)))
        add(f"literal_{n}_exact", data, n)
        add(f"literal_{n}_room", data, max(128, n + 64))
        if n:
            add(f"literal_{n}_short", data, n - 1)
    for off in [1, 2, 3, 4, 8, 14, 16, 18, 32, 64]:
        for count in [4, 7, 18, 19, 32, 33, 64, 65, 274, 529]:
            lits = bytes((i * 13 + 11) % 256 for i in range(off))
            data = match(lits, off, count) + literal(b"12345678")
            size = off + count + 8
            add(f"match_{off}_{count}_exact", data, size)
            add(f"match_{off}_{count}_room", data, max(128, size + 64))
            add(f"match_{off}_{count}_short", data, off + count - 1)
    # Many sequences, with short and long fields and overlap changes.
    chain = match(b"abcdefgh", 8, 18)
    chain += bytes([0x0f, 1, 0, 0])  # no literals, offset 1, length 19
    chain += bytes([0x04, 16, 0])    # no literals, offset 16, length 8
    chain += literal(bytes(range(32)))
    add("multiple_sequences", chain, 256)
    for name, data in [
        ("no_token", b""),
        ("missing_literal_extension", b"\xf0"),
        ("unterminated_literal_extension", b"\xf0\xff\xff"),
        ("missing_literals", b"\x50abc"),
        ("one_offset_byte", b"\x10a\x01"),
        ("zero_offset_slow", b"\x10a\x00\x00\x50abcde"),
        ("zero_offset_fast", b"\x10a\x00\x00\xf0\x00abcdefghijklmno"),
        ("offset_before_start_slow", b"\x10a\x02\x00\x50abcde"),
        ("offset_before_start_fast", b"\x10a\x02\x00\xf0\x00abcdefghijklmno"),
        ("match_missing_extension", b"\x1fa\x01\x00"),
        ("match_unterminated_extension", b"\x1fa\x01\x00\xff\xff"),
        ("no_final_token", b"\x10a\x01\x00"),
    ]:
        add(name, data, 256)
    # Accepted relaxed-end blocks, covered by R3 but not the strict R2 premise.
    add("relaxed_short_tail", match(b"a", 1, 4) + literal(b"b"), 128)
    add("relaxed_zero_tail", match(b"a", 1, 4) + literal(b""), 128)
    add("final_token_low_nibble", b"\x0f", 0)
    return result


def harness(tests):
    lines = ['(module',
             ' (import "decoder" "memory" (memory 32 32))',
             ' (import "decoder" "lz4_decompress" (func $decode (param i32 i32 i32 i32) (result i32)))',
             ' (func $assert (param i32) local.get 0 i32.eqz if unreachable end)',
             # Check every byte outside src/dst in the caller region. Source
             # bytes are checked too: only dst is allowed to change.
             ' (func $unchanged (param $src i32) (param $dst i32) (param $cap i32) (param $n i32)',
             '  (local $i i32) (local $v i32)',
             '  i32.const 131072 local.set $i',
             '  loop $scan',
             '   local.get $i local.get $dst i32.lt_u',
             '   local.get $i local.get $dst local.get $cap i32.add i32.ge_u i32.or',
             '   if',
             '    local.get $i local.get $src i32.lt_u',
             '    local.get $i local.get $src local.get $n i32.add i32.ge_u i32.or',
             '    if local.get $i i32.load8_u i32.const 165 i32.eq call $assert end',
             '   end',
             '   local.get $i i32.const 1 i32.add local.tee $i',
             '   i32.const 2097152 i32.lt_u br_if $scan',
             '  end)',
             ' (func (export "check") (result i32)']
    checks = 0
    for name, data, cap, expected, output in tests:
        # Both extremes of the allowed caller region, in both buffer orders.
        for src, dst in [(131072, 2097152 - cap), (2097152 - len(data), 131072)]:
            # Use addresses in the stated interval even for empty buffers.
            src = min(src, 2097151)
            dst = min(dst, 2097151)
            assert 131072 <= src and src + len(data) <= 2097152
            assert 131072 <= dst and dst + cap <= 2097152
            assert src + len(data) <= dst or dst + cap <= src
            lines.append(f'  ;; {checks}: {name}; src={src}, dst={dst}, n={len(data)}, cap={cap}')
            lines.append('  i32.const 131072 i32.const 165 i32.const 1966080 memory.fill')
            for i, b in enumerate(data):
                lines.append(f'  i32.const {src + i} i32.const {b} i32.store8')
            lines.append(f'  i32.const {src} i32.const {dst} i32.const {len(data)} i32.const {cap} call $decode')
            lines.append(f'  i32.const {expected} i32.eq call $assert')
            for i, b in enumerate(output):
                lines.append(f'  i32.const {dst + i} i32.load8_u i32.const {b} i32.eq call $assert')
            for i, b in enumerate(data):
                lines.append(f'  i32.const {src + i} i32.load8_u i32.const {b} i32.eq call $assert')
            lines.append(f'  i32.const {src} i32.const {dst} i32.const {cap} i32.const {len(data)} call $unchanged')
            checks += 1
    lines += [f'  i32.const {checks}', ' )', ')']
    return "\n".join(lines), checks


def main():
    artifact = ROOT / "lz4-flex.wasm"
    raw = artifact.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    if len(raw) != 7161 or actual != EXPECTED:
        raise SystemExit(f"artifact identity mismatch: {len(raw)} bytes, SHA256 {actual}")
    print(f"artifact: {len(raw)} bytes, SHA256 {actual}", flush=True)
    subprocess.run(["wasm-tools", "validate", str(artifact)], check=True)
    tests = cases()
    wat, count = harness(tests)
    with tempfile.TemporaryDirectory(prefix="lz4-check-") as temp:
        path = Path(temp)
        (path / "harness.wat").write_text(wat)
        subprocess.run(["wasm-tools", "parse", str(path / "harness.wat"),
                        "-o", str(path / "harness.wasm")], check=True)
        result = subprocess.run([
            "wasmtime", "-C", "cache=n", "--preload", f"decoder={artifact}",
            "--invoke", "check", str(path / "harness.wasm"),
        ], capture_output=True, text=True)
        if result.returncode:
            raise SystemExit(result.stderr)
        if result.stdout.strip() != str(count):
            raise SystemExit(f"unexpected harness result: {result.stdout!r}")
    print(f"PASS: {len(tests)} vectors, {count} original-artifact executions; "
          "return, successful output, and unchanged final memory outside dst checked.")
    print("LIMIT: finite executions; forbidden reads, transient writes, and universal R1/R2/R3 are not proved.")


if __name__ == "__main__":
    main()
