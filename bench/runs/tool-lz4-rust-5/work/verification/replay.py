#!/usr/bin/env python3
"""Deterministic artifact checks; finite evidence, not a universal proof."""
import hashlib
from pathlib import Path
import random
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
ARTIFACT = ROOT / "lz4-flex.wasm"
DIGEST = "1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775"
LOW, TOP = 131072, 2097152


def run(*args):
    subprocess.run(args, check=True, cwd=ROOT)


def quote(b):
    return '"' + ''.join(f'\\{v:02x}' for v in b) + '"'


def reference(data, cap):
    """Independent byte-wise sequence interpreter; returns bytes or None."""
    p, out = 0, bytearray()

    def extension(base):
        nonlocal p
        while True:
            if p == len(data):
                raise ValueError
            b = data[p]
            p += 1
            base += b
            if b != 255:
                return base

    try:
        while p < len(data):
            token = data[p]
            p += 1
            lit = token >> 4
            if lit == 15:
                lit = extension(15)
            if p + lit > len(data) or len(out) + lit > cap:
                return None
            out.extend(data[p:p + lit])
            p += lit
            if p == len(data):
                return bytes(out)
            if p + 2 > len(data):
                return None
            off = int.from_bytes(data[p:p + 2], 'little')
            p += 2
            length = (token & 15) + 4
            if length == 19:
                length = extension(19)
            if not 1 <= off <= len(out) or len(out) + length > cap:
                return None
            for _ in range(length):
                out.append(out[-off])
    except ValueError:
        pass
    return None


def ext(n):
    return bytes([255]) * (n // 255) + bytes([n % 255])


def sequence(literals, off=None, length=0):
    token = min(len(literals), 15) << 4
    if off is not None:
        assert 1 <= off <= 65535 and length >= 4
        token |= min(length - 4, 15)
    b = bytes([token])
    if len(literals) >= 15:
        b += ext(len(literals) - 15)
    b += literals
    if off is not None:
        b += off.to_bytes(2, 'little')
        if length >= 19:
            b += ext(length - 19)
    return b


def cases():
    rng = random.Random(0x4c5a34)
    result = []

    def add(label, data, cap, placement=0):
        out = reference(data, cap)
        src = LOW if placement != 2 else TOP - max(len(data), 1)
        dst = 1048576 if placement != 1 else TOP - max(cap, 1)
        assert 0 <= cap and src >= LOW and src + len(data) <= TOP
        assert dst >= LOW and dst + cap <= TOP
        assert src + len(data) <= dst or dst + cap <= src
        result.append((label, data, cap, src, dst, out))

    for n in list(range(34)) + [254, 255, 269, 270, 271, 525, 526, 4096]:
        data = sequence(bytes(rng.randrange(256) for _ in range(n)))
        for cap in sorted({max(0, n - 1), n, n + 80}):
            add(f'literals-{n}-cap-{cap}', data, cap, n % 3)
    for off in [1, 2, 3, 4, 7, 8, 16, 18, 32, 64, 255, 256, 65535]:
        for length in [4, 7, 18, 19, 32, 33, 64, 65, 274, 1024]:
            lits = bytes(rng.randrange(256) for _ in range(off))
            # Last match starts >=12 decoded bytes before the end (length+tail >=12).
            tail = bytes(rng.randrange(256) for _ in range(max(5, 12 - length)))
            data = sequence(lits, off, length) + sequence(tail)
            expected = lits + bytes(lits[i % off] for i in range(length)) + tail
            assert reference(data, len(expected)) == expected
            for cap in [len(expected) - 1, len(expected), len(expected) + 80]:
                add(f'match-{off}-{length}-cap-{cap}', data, cap, length % 3)
    for k in range(80):
        data, decoded = b'', b''
        for _ in range(rng.randrange(1, 8)):
            lit = bytes(rng.randrange(256) for _ in range(rng.randrange(1, 30)))
            decoded += lit
            off = rng.randrange(1, min(len(decoded), 65535) + 1)
            length = rng.randrange(7, 350)
            data += sequence(lit, off, length)
            for _ in range(length):
                decoded += decoded[-off:len(decoded) - off + 1] if off > 1 else decoded[-1:]
        tail = bytes(rng.randrange(256) for _ in range(rng.randrange(5, 32)))
        data += sequence(tail)
        decoded += tail
        assert reference(data, len(decoded)) == decoded
        add(f'multisequence-{k}', data, len(decoded) + (80 if k % 2 else 0), k % 3)
        add(f'truncated-{k}', data[:-rng.randrange(1, min(20, len(data)))], len(decoded) + 80)
    add('empty-byte-string', b'', 64)
    for b in range(256):
        add(f'one-byte-{b:02x}', bytes([b]), [0, 8, 64][b % 3])
    for k in range(400):
        data = bytes(rng.randrange(256) for _ in range(rng.randrange(0, 90)))
        add(f'arbitrary-{k}', data, rng.choice([0, 4, 16, 35, 80, 512]), k % 3)
    for data in [b'\x10A\x00\x00\x00', b'\x10A\x02\x00\x00', b'\x10A\x01\x00',
                 b'\x1fA\x01\x00', b'\xf0' + b'\xff' * 500, b'\x10A\x01\x00\x00']:
        add('special-' + data[:8].hex(), data, 4096)
    return result


# Instrument every load/store/copy/fill in the disassembled original, preserving
# its instruction and function indices. Additional named helpers are appended.
def instrument(wat):
    lines = wat.splitlines()
    out = []
    in_func = False
    pending_locals = False
    count = 0
    for line in lines[:-1]:
        if line.startswith('  (func '):
            in_func = True
            out.append(line)
            pending_locals = True
            continue
        if pending_locals and not line.strip().startswith('(local '):
            out.append('    (local $check_addr i32) (local $check_val32 i32)'
                       ' (local $check_val64 i64) (local $check_src i32) (local $check_len i32)')
            pending_locals = False
        if line == '  )':
            in_func = False
        op = line.strip().split()[0] if line.strip() else ''
        mem = re.fullmatch(r'(i32|i64)\.(load|store)(8|16|32)?(_[us])?', op)
        if in_func and mem:
            typ, action, bits, _ = mem.groups()
            width = int(bits or typ[1:]) // 8
            off = re.search(r'offset=(\d+)', line)
            off = int(off[1]) if off else 0
            if action == 'store':
                out.append(f'    local.set $check_val{typ[1:]}')
            out += ['    local.tee $check_addr', '    local.get $check_addr',
                    f'    i32.const {off}', f'    i32.const {width}',
                    '    call $check_read' if action == 'load' else '    call $check_write']
            if action == 'store':
                out.append(f'    local.get $check_val{typ[1:]}')
            count += 1
        elif in_func and op in ['memory.copy', 'memory.fill']:
            out += ['    local.set $check_len', '    local.set $check_src',
                    '    local.set $check_addr']
            if op == 'memory.copy':
                out += ['    local.get $check_src', '    i32.const 0',
                        '    local.get $check_len', '    call $check_read']
            out += ['    local.get $check_addr', '    i32.const 0',
                    '    local.get $check_len', '    call $check_write',
                    '    local.get $check_addr', '    local.get $check_src',
                    '    local.get $check_len']
            count += 1
        elif in_func and ('.load' in op or '.store' in op or op.startswith('memory.')):
            raise AssertionError('unhandled memory instruction: ' + line)
        out.append(line)
    out += ['  (global $src (mut i64) (i64.const 0))',
            '  (global $dst (mut i64) (i64.const 0))',
            '  (global $n (mut i64) (i64.const 0))',
            '  (global $cap (mut i64) (i64.const 0))',
            '''  (func (export "set_contract") (param i32 i32 i32 i32)
      local.get 0 i64.extend_i32_u global.set $src
      local.get 1 i64.extend_i32_u global.set $dst
      local.get 2 i64.extend_i32_u global.set $n
      local.get 3 i64.extend_i32_u global.set $cap)''']
    for access in ['read', 'write']:
        read_clause = '''local.get $a global.get $src i64.ge_u
          local.get $e global.get $src global.get $n i64.add i64.le_u i32.and i32.or''' if access == 'read' else ''
        out.append(f'''  (func $check_{access} (param $base i32) (param $off i32) (param $len i32)
      (local $a i64) (local $e i64)
      local.get $base i64.extend_i32_u local.get $off i64.extend_i32_u i64.add local.tee $a
      local.get $len i64.extend_i32_u i64.add local.set $e
      local.get $len i32.eqz
      local.get $e i64.const 131072 i64.le_u i32.or
      local.get $a global.get $dst i64.ge_u
      local.get $e global.get $dst global.get $cap i64.add i64.le_u i32.and i32.or
      {read_clause}
      i32.eqz if unreachable end)''')
    out.append(')')
    return '\n'.join(out), count


def harness(testcases, monitored):
    w = ['''(module $tests
      (import "dut" "memory" (memory 32 32))
      (import "dut" "lz4_decompress" (func $decode (param i32 i32 i32 i32) (result i32)))''']
    if monitored:
        w.append('(import "dut" "set_contract" (func $contract (param i32 i32 i32 i32)))')
    w.append('''(func $equal (param $a i32) (param $b i32) (param $n i32) (result i32)
      (local $i i32)
      block $done loop $next
        local.get $i local.get $n i32.ge_u br_if $done
        local.get $a local.get $i i32.add i32.load8_u
        local.get $b local.get $i i32.add i32.load8_u
        i32.ne if i32.const 0 return end
        local.get $i i32.const 1 i32.add local.set $i br $next
      end end i32.const 1)''')
    for k, (label, data, cap, src, dst, expected) in enumerate(testcases):
        w.append(f'(data $in{k} {quote(data)})')
        w.append(f'(data $out{k} {quote(expected or b"")})')
        args = f'i32.const {src} i32.const {dst} i32.const {len(data)} i32.const {cap}'
        w.append(f'''(func (export "case{k}") (result i32) (local $r i32)
          ;; {label}
          i32.const {LOW} i32.const 165 i32.const {TOP - LOW} memory.fill
          i32.const {src} i32.const 0 i32.const {len(data)} memory.init $in{k}
          {args + ' call $contract' if monitored else ''}
          {args} call $decode local.set $r
          local.get $r i32.const {len(expected) if expected is not None else -1} i32.ne
          if i32.const 0 return end
          i32.const 800000 i32.const 0 i32.const {len(data)} memory.init $in{k}
          i32.const {src} i32.const 800000 i32.const {len(data)} call $equal
          i32.eqz if i32.const 0 return end
          i32.const {dst - 1} i32.load8_u i32.const 165 i32.ne
          if i32.const 0 return end''')
        if dst + cap < TOP:
            w.append(f'i32.const {dst + cap} i32.load8_u i32.const 165 i32.ne if i32.const 0 return end')
        if expected is not None:
            w.append(f'''i32.const 600000 i32.const 0 i32.const {len(expected)} memory.init $out{k}
                i32.const {dst} i32.const 600000 i32.const {len(expected)} call $equal
                i32.eqz if i32.const 0 return end''')
        w.append('i32.const 1)')
    w.append(')')
    for k in range(len(testcases)):
        w.append(f'(assert_return (invoke $tests "case{k}") (i32.const 1))')
    return '\n'.join(w)


def main():
    original = ARTIFACT.read_bytes()
    assert len(original) == 7161 and hashlib.sha256(original).hexdigest() == DIGEST
    run('wasm-tools', 'validate', str(ARTIFACT))
    corpus = cases()
    with tempfile.TemporaryDirectory(prefix='lz4-check-') as td:
        td = Path(td)
        wat = subprocess.check_output(['wasm-tools', 'print', str(ARTIFACT)], text=True)
        monitored, count = instrument(wat)
        (td / 'monitored.wat').write_text(monitored)
        run('wasm-tools', 'parse', str(td / 'monitored.wat'), '-o', str(td / 'monitored.wasm'))
        run('wasm-tools', 'validate', str(td / 'monitored.wasm'))
        for label, module, checks in [('original', original, False),
                                      ('monitored', (td / 'monitored.wasm').read_bytes(), True)]:
            script = f'(module $dut binary {quote(module)})\n(register "dut" $dut)\n'
            script += harness(corpus, checks)
            path = td / (label + '.wast')
            path.write_text(script)
            run('wasmtime', 'wast', '-C', 'cache=n', str(path))
            print(f'{label}: {len(corpus)} cases PASS', flush=True)
    print(f'artifact SHA256 {DIGEST}; {count} memory instructions instrumented')
    print('PASS (finite replay only; no universal artifact claim)')


if __name__ == '__main__':
    main()
