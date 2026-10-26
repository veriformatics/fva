#!/usr/bin/env python3
"""Execute the original module with a minimal, fail-closed R allocator host."""
import hashlib
from pathlib import Path
import re
import struct
import subprocess

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "verification" / "generated"
SHA256 = "e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb"


def prepare():
    artifact = ROOT / "edgeR.so"
    data = artifact.read_bytes()
    assert len(data) == 96558
    assert hashlib.sha256(data).hexdigest() == SHA256
    OUT.mkdir(exist_ok=True)
    wat = subprocess.check_output(["wasm-tools", "print", str(artifact)], text=True)
    imports = re.findall(r'^  \(import "([^"]+)" "([^"]+)" (.*)\)$', wat, re.M)
    modules = {name: ["(module"] for name in ("env", "GOT.mem", "GOT.func")}
    modules["env"] += [
        '(global $heap (mut i32) (i32.const 65536))',
        '(global $allocs (export "allocs") (mut i32) (i32.const 0))',
        '(global $frees (export "frees") (mut i32) (i32.const 0))',
    ]
    for namespace, name, desc in imports:
        desc = re.sub(r'\(;.*?;\)', '', desc)
        desc = re.sub(r'\(type \d+\)', '', desc)
        if desc.startswith('(func'):
            if name == "R_chk_calloc":
                body = '''(local $p i32) (local $n i32)
                  local.get 0 local.get 1 i32.mul local.set $n
                  global.get $heap local.set $p
                  local.get $p local.get $n i32.add i32.const 7 i32.add
                  i32.const -8 i32.and global.set $heap
                  local.get $p i32.const 0 local.get $n memory.fill
                  global.get $allocs i32.const 1 i32.add global.set $allocs
                  local.get $p'''
            elif name == "R_chk_free":
                body = 'global.get $frees i32.const 1 i32.add global.set $frees'
            else:
                body = 'unreachable'
            decl = desc[:-1].replace('(func', f'(func (export "{name}")', 1)
            modules[namespace].append(decl + ' ' + body + ')')
        elif desc.startswith('(global'):
            value = {"__stack_pointer": 1500000, "__memory_base": 1024,
                     "__table_base": 1}.get(name, 0)
            decl = desc[:-1].replace('(global', f'(global (export "{name}")', 1)
            modules[namespace].append(decl + f' (i32.const {value}))')
        elif desc.startswith('(memory'):
            modules[namespace].append(f'(memory (export "{name}") 32)')
        elif desc.startswith('(table'):
            modules[namespace].append(f'(table (export "{name}") 32 funcref)')
        else:
            raise AssertionError(desc)
    for name, lines in modules.items():
        path = OUT / (name + '.wat')
        path.write_text('\n'.join(lines) + '\n)\n')
        subprocess.run(['wasm-tools', 'parse', str(path), '-o',
                        str(path.with_suffix('.wasm'))], check=True)

    driver = '''(module
      (import "env" "memory" (memory 32))
      (import "env" "allocs" (global $allocs (mut i32)))
      (import "env" "frees" (global $frees (mut i32)))
      (import "edgeR" "calc_cpm_raw" (func $raw (param i32 i32 i32 i32)))
      (func $matrix (export "matrix_entry")
        (param $rows i32) (param $cols i32)
        (param $c0 f64) (param $c1 f64) (param $c2 f64) (param $c3 f64)
        (param $L0 f64) (param $L1 f64) (param $index i32) (result f64)
        ;; Two 32-byte cmx structs at 32768,32800; L at 32864; cpm at 32880.
        ;; All fields are initialized; type=2 is a row-repeated double vector.
        local.get $rows i32.const 1 i32.lt_u if unreachable end
        local.get $rows i32.const 2 i32.gt_u if unreachable end
        local.get $cols i32.const 1 i32.lt_u if unreachable end
        local.get $cols i32.const 2 i32.gt_u if unreachable end
        local.get $index local.get $rows local.get $cols i32.mul
        i32.ge_u if unreachable end
        i32.const 32768 i32.const 0 i32.const 144 memory.fill
        i32.const 32768 i32.const 32880 i32.store
        i32.const 32776 local.get $rows i32.store
        i32.const 32780 local.get $cols i32.store
        i32.const 32792 local.get $rows i32.store
        i32.const 32800 i32.const 32864 i32.store
        i32.const 32808 local.get $rows i32.store
        i32.const 32812 local.get $cols i32.store
        i32.const 32816 i32.const 2 i32.store
        i32.const 32824 i32.const 1 i32.store
        i32.const 32864 local.get $L0 f64.store
        i32.const 32872 local.get $L1 f64.store
        i32.const 32880 local.get $c0 f64.store
        i32.const 32888 local.get $c1 f64.store
        i32.const 32896 local.get $c2 f64.store
        i32.const 32904 local.get $c3 f64.store
        i32.const 0 global.set $allocs
        i32.const 0 global.set $frees
        i32.const 32768 i32.const 32800 i32.const 32880 i32.const 1 call $raw
        global.get $allocs i32.const 2 i32.ne if unreachable end
        global.get $frees i32.const 2 i32.ne if unreachable end
        i32.const 32880 local.get $index i32.const 3 i32.shl i32.add f64.load)
      (func $run (export "run") (param $c f64) (param $L f64) (result f64)
        i32.const 1 i32.const 1
        local.get $c f64.const 0 f64.const 0 f64.const 0
        local.get $L f64.const 0 i32.const 0 call $matrix)
      (func (export "bits") (param f64 f64) (result i64)
        local.get 0 local.get 1 call $run i64.reinterpret_f64)
    )'''
    path = OUT / 'driver.wat'
    path.write_text(driver + '\n')
    subprocess.run(['wasm-tools', 'parse', str(path), '-o',
                    str(OUT / 'driver.wasm')], check=True)


def command(export, count, libsize):
    args = ['wasmtime', 'run', '-C', 'cache=n']
    for name in ('env', 'GOT.mem', 'GOT.func'):
        args += ['--preload', f'{name}={OUT / (name + ".wasm")}']
    return args + ['--preload', f'edgeR={ROOT / "edgeR.so"}',
                   '--invoke', export, str(OUT / 'driver.wasm'), str(count), str(libsize)]


def run(export, count, libsize):
    result = subprocess.run(command(export, count, libsize), check=True,
                            text=True, capture_output=True)
    return result.stdout.strip()


if __name__ == '__main__':
    prepare()
    cases = [('10', '1000000', 0x4024000000000000),
             ('10', '18', 0x4120f4471c71c71c),
             ('1e308', '1e308', 0x7ff0000000000000)]
    for count, libsize, expected in cases:
        bits = int(run('bits', count, libsize)) & ((1 << 64) - 1)
        assert bits == expected, (count, libsize, hex(bits), hex(expected))
        value = struct.unpack('>d', bits.to_bytes(8, 'big'))[0]
        print(f'calc_cpm_raw(c={count}, L={libsize}) = {value!r}; bits={bits:016x}')
    print('PASS: original artifact hash, control case, R2 boundary, R1 overflow witness')
