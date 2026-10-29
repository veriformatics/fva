#!/usr/bin/env python3
"""Exact-artifact regression checks and dynamic R1 instrumentation; no proof claim."""
import hashlib
import random
import re
import subprocess
import struct
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LOW, HIGH = 131072, 2097152
DIGEST = '1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775'


def run(args):
    result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(f'{args}:\n{result.stdout}\n{result.stderr}')
    return result.stdout


def reference(data, cap):
    """Format interpreter, accepting relaxed end conditions permitted by R3."""
    p, out = 0, bytearray()

    def length(small, bias):
        nonlocal p
        n = small + bias
        if small == 15:
            while True:
                if p == len(data):
                    raise ValueError('unterminated length')
                b = data[p]
                p += 1
                n += b
                if b != 255:
                    break
        return n

    try:
        while p < len(data):
            token = data[p]
            p += 1
            ll = length(token >> 4, 0)
            if p + ll > len(data) or len(out) + ll > cap:
                return None
            out.extend(data[p:p + ll])
            p += ll
            if p == len(data):
                return bytes(out)
            if p + 2 > len(data):
                return None
            off = data[p] + 256 * data[p + 1]
            p += 2
            ml = length(token & 15, 4)
            if not 1 <= off <= len(out) or len(out) + ml > cap:
                return None
            for _ in range(ml):
                out.append(out[-off])
    except ValueError:
        pass
    return None


def extra(n):
    return bytes([255]) * (n // 255) + bytes([n % 255])


def sequence(literals, off=None, ml=4, final_low=0):
    ll = len(literals)
    low = final_low if off is None else min(ml - 4, 15)
    result = bytes([(min(ll, 15) << 4) | low])
    if ll >= 15:
        result += extra(ll - 15)
    result += literals
    if off is not None:
        result += off.to_bytes(2, 'little')
        if ml >= 19:
            result += extra(ml - 19)
    return result


def cases():
    tests = []

    def add(label, data, cap, src=LOW + 16, dst=1048592):
        assert LOW <= src <= src + len(data) <= HIGH
        assert LOW <= dst <= dst + cap <= HIGH
        assert not data or not cap or src + len(data) <= dst or dst + cap <= src
        expected = reference(data, cap)
        tests.append((label, data, cap, src, dst, expected))

    add('empty compressed input', b'', 0)
    add('empty content', b'\0', 0)
    add('minimal valid independent match', bytes.fromhex('13 41 01 00 50 42 43 44 45 46'), 13)
    add('maximal input extent', b'\xf0' + b'\xff' * (HIGH - LOW - 1), 0, LOW, LOW)
    add('maximal destination extent', b'\0', HIGH - LOW - 1, HIGH - 1, LOW)
    large_literals = bytes(range(256)) * 3812
    large_block = sequence(large_literals)
    add('large literal block with adjacent buffers', large_block, len(large_literals),
        LOW, LOW + len(large_block))
    for token in range(256):
        literals = bytes(range(token >> 4))
        data = sequence(literals, final_low=token & 15)
        for spare in (0, 64):
            add(f'final token {token:02x}, spare {spare}', data, len(literals) + spare)
    for ll in (1, 2, 3, 4, 7, 8, 14, 15, 16, 17, 31, 32, 33, 64, 254, 255, 256,
               270, 280, 512, 4096, 65536):
        literals = bytes((i * 17 + 9) % 256 for i in range(ll))
        data = sequence(literals)
        add(f'literals {ll}', data, ll)
        add(f'literals {ll} too small', data, ll - 1)
    for off in range(1, 65):
        literals = bytes((i * 71 + off) % 256 for i in range(off))
        for ml in (4, 7, 18, 19, 32, 33, 64, 65, 274):
            data = sequence(literals, off, ml) + sequence(b'last literals')
            size = off + ml + 13
            add(f'match off={off}, len={ml}, exact', data, size)
            add(f'match off={off}, len={ml}, spare', data, size + 128)
            if ml in (4, 19, 65):
                add(f'match off={off}, len={ml}, too small', data, size - 1)
    for n in (0, 1, 2, 16, 255, 4096, 1048576):
        add(f'unterminated literal length {n}', b'\xf0' + b'\xff' * n, 0)
        add(f'unterminated match length {n}', b'\x1fA\x01\0' + b'\xff' * n, 0)
    for data in (b'\0\0\0', b'\x10A\0\0', b'\x10A\x02\0', b'\x0f\x01\0',
                 b'\x10A\x01\0', b'\x10A\x01\0\0', b'\x10A\x01', b'\xf0'):
        add('malformed or relaxed ending ' + data.hex(), data, 256)
    rng = random.Random(0x4C5A34)
    valid = []
    for k in range(192):
        data, size = b'', 0
        for j in range(rng.randrange(1, 8)):
            ll = rng.randrange(1, 40)
            literals = rng.randbytes(ll)
            size += ll
            off = rng.randrange(1, min(size, 65535) + 1)
            ml = rng.randrange(4, 600)
            data += sequence(literals, off, ml)
            size += ml
        tail = rng.randbytes(rng.randrange(12, 40))
        data += sequence(tail)
        size += len(tail)
        valid.append(data)
        add(f'multiple sequences {k}', data, size + rng.choice((0, 1, 32, 128)))
        cut = rng.randrange(len(data))
        add(f'truncated sequences {k}', data[:cut], size + 64)
        changed = bytearray(data)
        changed[rng.randrange(len(data))] = rng.randrange(256)
        add(f'mutated sequences {k}', bytes(changed), size + 64)
    for k in range(256):
        data = rng.randbytes(rng.randrange(65))
        add(f'arbitrary bytes {k}', data, rng.randrange(257))
    add('lower and upper boundary', sequence(b'boundary'), 8, LOW, HIGH - 8)
    add('reverse buffer order', sequence(b'order'), 5, HIGH - 6, LOW)
    return tests


AUDIT = r'''
  (global $audit_src (mut i64) (i64.const 0))
  (global $audit_dst (mut i64) (i64.const 0))
  (global $audit_n (mut i64) (i64.const 0))
  (global $audit_cap (mut i64) (i64.const 0))
  (func (export "audit_set") (param i32 i32 i32 i32)
    local.get 0 i64.extend_i32_u global.set $audit_src
    local.get 1 i64.extend_i32_u global.set $audit_dst
    local.get 2 i64.extend_i32_u global.set $audit_n
    local.get 3 i64.extend_i32_u global.set $audit_cap)
  (func $audit (param $base i32) (param $offset i32) (param $width i32)
      (param $write i32) (result i32)
    (local $lo i64) (local $hi i64) (local $ok i32)
    local.get $base i64.extend_i32_u
    local.get $offset i64.extend_i32_u i64.add local.set $lo
    local.get $lo local.get $width i64.extend_i32_u i64.add local.set $hi
    local.get $width i32.eqz
    if local.get $base return end
    local.get $lo i64.const 2097152 i64.lt_u
    local.get $hi i64.const 131072 i64.gt_u i32.and
    if
      local.get $lo i64.const 131072 i64.lt_u
      if i64.const 131072 local.set $lo end
      local.get $hi i64.const 2097152 i64.gt_u
      if i64.const 2097152 local.set $hi end
      local.get $lo global.get $audit_dst i64.ge_u
      local.get $hi global.get $audit_dst global.get $audit_cap i64.add i64.le_u
      i32.and local.set $ok
      local.get $write i32.eqz
      if
        local.get $ok
        local.get $lo global.get $audit_src i64.ge_u
        local.get $hi global.get $audit_src global.get $audit_n i64.add i64.le_u
        i32.and i32.or local.set $ok
      end
      local.get $ok i32.eqz if unreachable end
    end
    local.get $base)
'''


def instrument(wat):
    """Append locals so all original numeric function/local indices remain unchanged."""
    lines = wat.splitlines()
    output = []
    i = 0
    counts = {'load': 0, 'store': 0, 'copy': 0, 'fill': 0}
    while i < len(lines):
        line = lines[i]
        if re.match(r'  \(func \(;\d+;\)', line):
            output.append(line)
            if i + 1 < len(lines) and lines[i + 1].lstrip().startswith('(local '):
                i += 1
                output.append(lines[i])
            output.append('    (local $audit_base i32) (local $audit_i32 i32) '
                          '(local $audit_i64 i64) (local $audit_len i32) '
                          '(local $audit_from i32) (local $audit_to i32)')
        else:
            match = re.fullmatch(r'\s*(i32|i64)\.(load(?:8_u|16_u)?|store(?:8|16)?)(.*)', line)
            if match:
                ty, op, attrs = match.groups()
                is_store = op.startswith('store')
                width = 1 if '8' in op else 2 if '16' in op else 4 if ty == 'i32' else 8
                found = re.search(r'offset=(\d+)', attrs)
                offset = int(found[1]) if found else 0
                if is_store:
                    output.append(f'    local.set $audit_{ty}')
                output.extend((f'    i32.const {offset}', f'    i32.const {width}',
                               f'    i32.const {int(is_store)}', '    call $audit'))
                if is_store:
                    output.append(f'    local.get $audit_{ty}')
                output.append(line)
                counts['store' if is_store else 'load'] += 1
            elif line.strip() in ('memory.copy', 'memory.fill'):
                copy = line.strip() == 'memory.copy'
                output.extend(('    local.set $audit_len',
                               '    local.set $audit_from', '    local.set $audit_to'))
                if copy:
                    output.extend(('    local.get $audit_from', '    i32.const 0',
                                   '    local.get $audit_len', '    i32.const 0',
                                   '    call $audit', '    drop'))
                output.extend(('    local.get $audit_to', '    i32.const 0',
                               '    local.get $audit_len', '    i32.const 1',
                               '    call $audit', '    local.get $audit_from',
                               '    local.get $audit_len', line))
                counts['copy' if copy else 'fill'] += 1
            else:
                # Refuse to silently skip an unrecognized memory operation.
                assert not re.search(r'\b(?:i32|i64)\.(?:load|store)|\bmemory\.', line), line
                output.append(line)
        i += 1
    assert output[-1].endswith(')'), 'module closing delimiter'
    output[-1] = output[-1][:-1]  # wasm-tools places module ')' after the data segment.
    output.append(AUDIT)
    output.append(')')
    assert counts == {'load': 104, 'store': 107, 'copy': 5, 'fill': 3}, counts
    return '\n'.join(output)


def quote(data):
    return '"' + ''.join(f'\\{b:02x}' for b in data) + '"'


HELPERS = r'''
  (memory $oracle 64 64)
  (func $equal (param $p i32) (param $q i32) (param $n i32)
    (local $i i32)
    block $done loop $again
      local.get $i local.get $n i32.ge_u br_if $done
      local.get $p local.get $i i32.add i32.load8_u
      local.get $q local.get $i i32.add i32.load8_u $oracle
      i32.ne if unreachable end
      local.get $i i32.const 1 i32.add local.set $i br $again
    end end)
  (func $guard (param $p i32) (param $n i32)
    (local $i i32)
    block $done loop $again
      local.get $i local.get $n i32.ge_u br_if $done
      local.get $p local.get $i i32.add i32.load8_u
      i32.const 165 i32.ne if unreachable end
      local.get $i i32.const 1 i32.add local.set $i br $again
    end end)
'''


def make_wast(module, tests, audited):
    out = ['(module $sut binary ' + quote(module) + ')', '(register "sut" $sut)',
           '(module $tests', '  (import "sut" "memory" (memory 32 32))',
           '  (import "sut" "lz4_decompress" (func $decode (param i32 i32 i32 i32) (result i32)))']
    if audited:
        out.append('  (import "sut" "audit_set" (func $set (param i32 i32 i32 i32)))')
    out.append(HELPERS)
    for i, (label, data, cap, src, dst, expected) in enumerate(tests):
        out.append(f'  (data $in{i} {quote(data)})')
        out.append(f'  (data $out{i} {quote(expected or b"")})')
        out.append(f'  (func (export "case{i}") (result i32) (local $result i32)')
        # Guard only addresses outside both buffers, including when cap is zero.
        guards = sorted({p for start, size in ((src, len(data)), (dst, cap))
                         for p in list(range(max(0, start - 8), start))
                         + list(range(start + size, min(HIGH, start + size + 8)))
                         if not src <= p < src + len(data) and not dst <= p < dst + cap})
        intervals = []
        for p in guards:
            if intervals and intervals[-1][0] + intervals[-1][1] == p:
                intervals[-1][1] += 1
            else:
                intervals.append([p, 1])
        for p, n in intervals:
            out.append(f'    i32.const {p} i32.const 165 i32.const {n} memory.fill')
        out.append(f'    i32.const {dst} i32.const 90 i32.const {cap} memory.fill')
        out.append(f'    i32.const {src} i32.const 0 i32.const {len(data)} memory.init $in{i}')
        out.append(f'    i32.const 0 i32.const 0 i32.const {len(data)} memory.init $oracle $in{i}')
        if expected is not None:
            out.append(f'    i32.const {HIGH} i32.const 0 i32.const {len(expected)} memory.init $oracle $out{i}')
        if audited:
            out.append(f'    i32.const {src} i32.const {dst} i32.const {len(data)} i32.const {cap} call $set')
        out.append(f'    i32.const {src} i32.const {dst} i32.const {len(data)} i32.const {cap} call $decode local.set $result')
        out.append(f'    i32.const {src} i32.const 0 i32.const {len(data)} call $equal')
        if expected is not None:
            out.append(f'    i32.const {dst} i32.const {HIGH} i32.const {len(expected)} call $equal')
        for p, n in intervals:
            out.append(f'    i32.const {p} i32.const {n} call $guard')
        out.append('    local.get $result)')
    out.append(')')
    for i, (label, data, cap, src, dst, expected) in enumerate(tests):
        result = -1 if expected is None else len(expected)
        out.append(f';; {i}: {label}')
        out.append(f'(assert_return (invoke $tests "case{i}") (i32.const {result}))')
    return '\n'.join(out)


def verified_oracle(tmp, tests):
    binary = tmp / 'model-oracle'
    print(run(['verus', '--no-cheating', '--compile', 'verification/model.rs', '-o', str(binary)]).strip(), flush=True)
    corpus = bytearray(struct.pack('<I', len(tests)))
    for _, data, cap, _, _, _ in tests:
        corpus += struct.pack('<II', len(data), cap) + data
    checked = subprocess.run([str(binary)], input=corpus, capture_output=True, check=True).stdout
    cursor = 0
    for label, _, _, _, _, expected in tests:
        result, = struct.unpack_from('<i', checked, cursor)
        cursor += 4
        actual = None if result == -1 else checked[cursor:cursor + result]
        if result != -1:
            assert result >= 0
            cursor += result
        assert actual == expected, ('Python/verified model disagreement', label)
    assert cursor == len(checked)
    print('PASS: Python format oracle agrees byte-for-byte with compiled Verus model', flush=True)


def main():
    if not __debug__:
        raise SystemExit('Python assertions must be enabled (do not use -O).')
    artifact = (ROOT / 'lz4-flex.wasm').read_bytes()
    assert len(artifact) == 7161
    assert hashlib.sha256(artifact).hexdigest() == DIGEST
    print(f'artifact: {len(artifact)} bytes, sha256 {DIGEST}', flush=True)
    run(['wasm-tools', 'validate', 'lz4-flex.wasm'])
    wat = run(['wasm-tools', 'print', 'lz4-flex.wasm'])
    tests = cases()
    assert len({test[0] for test in tests}) == len(tests)
    with tempfile.TemporaryDirectory(prefix='lz4-verification-') as tmp:
        tmp = Path(tmp)
        verified_oracle(tmp, tests)
        audit_wat, audit_wasm = tmp / 'audited.wat', tmp / 'audited.wasm'
        audit_wat.write_text(instrument(wat))
        run(['wasm-tools', 'parse', str(audit_wat), '-o', str(audit_wasm)])
        run(['wasm-tools', 'validate', str(audit_wasm)])
        for audited, module in ((False, artifact), (True, audit_wasm.read_bytes())):
            script = tmp / ('audited.wast' if audited else 'original.wast')
            script.write_text(make_wast(module, tests, audited))
            print(f'checking {len(tests)} cases on {"instrumented" if audited else "original"} Wasm...', flush=True)
            run(['wasmtime', 'wast', '-C', 'cache=n', str(script)])
            print('PASS: all returns, successful output bytes, source bytes, and guards match', flush=True)
    print('PASS: every instrumented high-memory access stayed within the R1 buffers in these executions')
    print('These finite execution checks do not prove universal R1, R2, or R3.')


if __name__ == '__main__':
    main()
