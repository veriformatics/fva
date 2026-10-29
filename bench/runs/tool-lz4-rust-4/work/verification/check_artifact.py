#!/usr/bin/env python3
"""Finite checks on the exact shipped bytes. NOT a universal proof or read trace.
Uses Wasmtime's WAST runner; no Python packages or network are needed.
"""
import hashlib
import os
from pathlib import Path
import random
import subprocess
import tempfile

if not __debug__:
    raise SystemExit('Python assertion checks must be enabled')

ROOT = Path(__file__).resolve().parent.parent
ARTIFACT = ROOT / 'lz4-flex.wasm'
SHA = '1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775'
LOW, TOP, SENTINEL = 131072, 2097152, 165


def reference(data, cap, strict=False):
    """Simple independent block parser, allowing only the end-condition relaxation."""
    p, out, last_match_start = 0, bytearray(), None

    def length(n):
        nonlocal p
        if n == 15:
            while True:
                if p == len(data):
                    raise ValueError('unterminated extension')
                b = data[p]
                p += 1
                n += b
                if b != 255:
                    break
        return n

    try:
        while True:
            if p == len(data):
                return None
            token = data[p]
            p += 1
            ll = length(token >> 4)
            if ll > len(data) - p or ll > cap - len(out):
                return None
            out += data[p:p + ll]
            p += ll
            if p == len(data):
                if strict and last_match_start is not None:
                    if ll < 5 or len(out) - last_match_start < 12:
                        return None
                return bytes(out)
            if len(data) - p < 2:
                return None
            off = data[p] + 256 * data[p + 1]
            p += 2
            ml = 4 + length(token & 15)
            if off == 0 or off > len(out) or ml > cap - len(out):
                return None
            last_match_start = len(out)
            for _ in range(ml):
                out.append(out[-off])
    except ValueError:
        return None


def ext(n):
    return bytes([255]) * (n // 255) + bytes([n % 255])


def sequence(literals, off, ml):
    assert 1 <= off <= 65535 and ml >= 4
    ll = len(literals)
    return (bytes([(min(ll, 15) << 4) | min(ml - 4, 15)])
            + (ext(ll - 15) if ll >= 15 else b'') + literals
            + off.to_bytes(2, 'little') + (ext(ml - 19) if ml >= 19 else b''))


def final(literals, low=0):
    ll = len(literals)
    return (bytes([(min(ll, 15) << 4) | low])
            + (ext(ll - 15) if ll >= 15 else b'') + literals)


def runs(data):
    i = 0
    while i < len(data):
        j = i + 1
        while j < len(data) and data[j] == data[i]:
            j += 1
        yield i, j - i, data[i]
        i = j


def cases():
    result = []

    def add(name, data, cap, layout=0, valid=False):
        if layout == 0:
            src, dst = LOW, 1048576
        elif layout == 1:
            src, dst = 1048576, LOW
        elif layout == 2:
            src, dst = TOP - max(len(data), 1), LOW
        else:
            src, dst = LOW, TOP - max(cap, 1)
        assert LOW <= src and src + len(data) <= TOP
        assert LOW <= dst and dst + cap <= TOP
        assert src + len(data) <= dst or dst + cap <= src
        expected = reference(data, cap)
        assert not valid or (expected is not None and reference(data, cap, strict=True) == expected)
        result.append((name, data, cap, src, dst, expected, valid))

    for ll in list(range(41)) + [254, 255, 269, 270, 271, 284, 285, 4096]:
        data = final(bytes((i * 37 + 9) % 256 for i in range(ll)))
        for cap in sorted({max(0, ll - 1), ll, ll + 1, ll + 34}):
            add(f'literal-{ll}-cap-{cap}', data, cap, cap % 4, cap >= ll)
    # Last-token low bits have no match field, including low == 15.
    for low in range(16):
        add(f'final-low-{low}', final(b'abcde', low), 39, low % 4, True)
    for prefix_len in [1, 2, 4, 8, 14, 15, 17, 32, 64]:
        prefix = bytes((i * 13 + 33) % 256 for i in range(prefix_len))
        for off in sorted({1, min(2, prefix_len), prefix_len}):
            for ml in [4, 7, 14, 18, 19, 20, 32, 33, 64, 65, 270]:
                tail = b'tail-literals-0123456789ABCDE'
                data = sequence(prefix, off, ml) + final(tail)
                size = prefix_len + ml + len(tail)
                for cap in [size - 1, size, size + 34]:
                    add(f'match-{prefix_len}-{off}-{ml}-cap-{cap}', data,
                        cap, (ml + off) % 4, cap >= size)
    # Multiple sequences, including extended match/literal lengths.
    data = (sequence(b'ab', 2, 300) + sequence(bytes(range(64)), 300, 100)
            + sequence(b'', 1, 18) + final(b'final five or more'))
    size = len(reference(data, 2000))
    for cap in [size - 1, size, size + 64]:
        add('multi-sequence', data, cap, cap % 4, cap >= size)
    malformed = [b'', b'\xf0', b'\xf0\xff', b'\x10', b'\x00\x01',
                 b'\x00\x00\x00', b'\x10a\x00\x00', b'\x10a\x02\x00',
                 b'\x1fa\x01\x00', b'\x1fa\x01\x00\xff',
                 b'\x10a\x01\x00', b'\x00\xff\xff\x00']
    for i, data in enumerate(malformed):
        for cap in [0, 1, 4, 5, 34, 35, 256]:
            add(f'malformed-{i}-{cap}', data, cap, i % 4)
    # R3 allows violations of end restrictions, but no malformed sequence.
    for data in [b'\x10a\x01\x00\x00', b'\x10a\x01\x00\x10b',
                 b'\x10a\x01\x00\x0f']:
        add('relaxed-end-conditions', data, 64)
    rng = random.Random(0x4C5A34)
    seeds = [c[1] for c in result if len(c[1]) < 512]
    for i in range(400):
        if i % 2:
            data = bytearray(rng.choice(seeds))
            if data:
                data[rng.randrange(len(data))] = rng.randrange(256)
        else:
            data = bytearray(rng.randbytes(rng.randrange(65)))
        add(f'mutated-or-random-{i}', bytes(data), rng.randrange(513), i % 4)
    # Maximal source region disjoint from a one-byte destination. These tests
    # exercise extension sums near the maximum possible under the README.
    add('maximum-unterminated-extension', b'\xf0' + b'\xff' * (TOP - LOW - 2), 1, 3)
    add('maximum-terminated-extension', b'\xf0' + b'\xff' * (TOP - LOW - 3) + b'\x00', 1, 3)
    return result


PRELUDE = r'''
(module $tests
  (import "decoder" "memory" (memory 32 32))
  (import "decoder" "lz4_decompress" (func $decode (param i32 i32 i32 i32) (result i32)))
  (func $check_run (param $p i32) (param $n i32) (param $v i32)
    (local $end i32)
    local.get $p local.get $n i32.add local.set $end
    block $done
      loop $loop
        local.get $p local.get $end i32.eq br_if $done
        local.get $p i32.load8_u local.get $v i32.ne
        if unreachable end
        local.get $p i32.const 1 i32.add local.set $p
        br $loop
      end
    end)
  (func $guards (param $src i32) (param $n i32) (param $dst i32) (param $cap i32)
    (local $p i32)
    i32.const 131072 local.set $p
    block $done
      loop $loop
        local.get $p i32.const 2097152 i32.eq br_if $done
        local.get $p local.get $src i32.eq local.get $n i32.eqz i32.eqz i32.and
        if local.get $p local.get $n i32.add local.set $p br $loop end
        local.get $p local.get $dst i32.eq local.get $cap i32.eqz i32.eqz i32.and
        if local.get $p local.get $cap i32.add local.set $p br $loop end
        local.get $p i32.load8_u i32.const 165 i32.ne if unreachable end
        local.get $p i32.const 1 i32.add local.set $p
        br $loop
      end
    end)
'''


def main():
    binary = ARTIFACT.read_bytes()
    assert hashlib.sha256(binary).hexdigest() == SHA, 'artifact hash mismatch'
    assert len(binary) == 7161
    subprocess.run(['wasm-tools', 'validate', str(ARTIFACT)], check=True)
    tests = cases()
    with tempfile.TemporaryDirectory(prefix='lz4-artifact-check-') as tmp:
        wast = Path(tmp) / 'check.wast'
        with wast.open('w') as f:
            f.write('(module $decoder binary "' + ''.join(f'\\{b:02x}' for b in binary) + '")\n')
            f.write('(register "decoder" $decoder)\n')
            f.write(PRELUDE)
            for i, (name, data, cap, src, dst, expected, _) in enumerate(tests):
                f.write(f'  ;; {i}: {name}\n  (func (export "case_{i}")\n')
                f.write(f'    i32.const {LOW} i32.const {SENTINEL} i32.const {TOP - LOW} memory.fill\n')
                for off, n, val in runs(data):
                    f.write(f'    i32.const {src + off} i32.const {val} i32.const {n} memory.fill\n')
                ret = -1 if expected is None else len(expected)
                f.write(f'    i32.const {src} i32.const {dst} i32.const {len(data)} i32.const {cap} call $decode\n')
                f.write(f'    i32.const {ret} i32.ne if unreachable end\n')
                for off, n, val in runs(data):
                    f.write(f'    i32.const {src + off} i32.const {n} i32.const {val} call $check_run\n')
                if expected is not None:
                    for off, n, val in runs(expected):
                        f.write(f'    i32.const {dst + off} i32.const {n} i32.const {val} call $check_run\n')
                f.write(f'    i32.const {src} i32.const {len(data)} i32.const {dst} i32.const {cap} call $guards\n  )\n')
            f.write(')\n')
            for i in range(len(tests)):
                f.write(f'(assert_return (invoke $tests "case_{i}"))\n')
        env = dict(os.environ, XDG_CACHE_HOME=str(Path(tmp) / 'cache'))
        subprocess.run(['wasmtime', 'wast', str(wast)], check=True, env=env)
    print(f'artifact SHA-256: {SHA}')
    print(f'PASS: {len(tests)} exact-binary cases; {sum(c[-1] for c in tests)} generated format-valid cases')
    print('Each case checks return, successful output, unchanged source, and every byte outside both buffers.')
    print('Finite execution checks do not establish universal R1/R2/R3 or constrain reads.')


if __name__ == '__main__':
    main()
