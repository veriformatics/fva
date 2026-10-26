#!/usr/bin/env python3
"""Invoke unchanged edgeR.so with a minimal, trapping R/Emscripten host.

Only calloc/free implement C runtime behavior. Unused functions trap, including
R entry points; __cxa_atexit and pthread_mutex_init support static constructors.
The test wrapper writes two cmx structs and calls the actual exported function.
"""
import hashlib
from pathlib import Path
import re
import struct
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
EXPECTED = 'e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb'


def run(counts, libraries):
    artifact = ROOT / 'edgeR.so'
    assert hashlib.sha256(artifact.read_bytes()).hexdigest() == EXPECTED
    assert len(counts) == len(libraries) and len(counts) > 0
    assert len(counts) <= 128
    with tempfile.TemporaryDirectory(prefix='edger-cpm-') as tmp:
        tmp = Path(tmp)
        subprocess.run(['wasm-tools', 'print', str(artifact), '-o', str(tmp / 'original.wat')], check=True)
        wat = (tmp / 'original.wat').read_text()
        types = dict(re.findall(r'^  \(type \(;(\d+);\) (\(func(?: .*)?\))\)$', wat, re.M))
        hosts = {name: ['(module'] for name in ['env', 'GOT.mem', 'GOT.func']}
        env = hosts['env']
        env += ['(memory (export "memory") 32)', '(table (export "__indirect_function_table") 128 funcref)',
                '(global $heap (mut i32) (i32.const 131072))']
        for name, typ in re.findall(r'^  \(import "env" "([^"]+)" \(func .*?\(type (\d+)\)', wat, re.M):
            signature = types[typ][len('(func'):-1]
            body = 'unreachable'
            if name == 'R_chk_calloc':
                # This fresh memory is zero; allocations do not overlap, so calloc is exact.
                body = ('(local $p i32) global.get $heap local.set $p '
                        'global.get $heap local.get 0 local.get 1 i32.mul i32.add '
                        'i32.const 7 i32.add i32.const -8 i32.and global.set $heap '
                        'global.get $heap i32.const 1048576 i32.gt_u if unreachable end local.get $p')
            elif name == 'R_chk_free':
                body = ''  # No reuse is needed for these bounded runs.
            elif name in ['__cxa_atexit', 'pthread_mutex_init']:
                body = 'i32.const 0'
            env.append(f'(func (export "{name}") {signature} {body})')
        for module, name, typ in re.findall(r'^  \(import "([^"]+)" "([^"]+)" \(global .*?\) (.*?)\)\)$', wat, re.M):
            value = {'__stack_pointer': 1048576, '__memory_base': 4096, '__table_base': 1}.get(name, 0)
            hosts[module].append(f'(global (export "{name}") {typ} (i32.const {value}))')
        for name, lines in hosts.items():
            (tmp / f'{name}.wat').write_text('\n'.join(lines + [')']))
        # Data at 65536 is above module data (4096..24564), below heap and stack.
        n = len(counts)
        data = struct.pack('<8I', 66048, 0, 1, n, 0, 0, 1, 0)
        data += struct.pack('<8I', 67072, 0, 1, n, 2, 0, 1, 0)
        escaped = ''.join(f'\\{b:02x}' for b in data)
        initialize = []
        for address, values in [(66048, counts), (67072, libraries)]:
            for i, value in enumerate(values):
                initialize.append(f'i32.const {address+8*i} f64.const {float(value).hex()} f64.store')
        results = ' '.join('f64' for _ in counts)
        loads = ' '.join(f'i32.const {66048+8*i} f64.load' for i in range(n))
        wrapper = f'''(module
          (import "env" "memory" (memory 32))
          (import "edgeR" "calc_cpm_raw" (func $cpm (param i32 i32 i32 i32)))
          (data (i32.const 65536) "{escaped}")
          (func (export "run") (result {results})
            {' '.join(initialize)}
            i32.const 65536 i32.const 65568 i32.const 66048 i32.const 1 call $cpm
            {loads}))'''
        (tmp / 'wrapper.wat').write_text(wrapper)
        command = ['wasmtime', 'run', '-C', 'cache=n']
        for name in hosts:
            command += ['--preload', f'{name}={tmp / (name + ".wat")}']
        command += ['--preload', f'edgeR={artifact}', '--invoke', 'run', str(tmp / 'wrapper.wat')]
        result = subprocess.run(command, capture_output=True, text=True)
        if result.returncode:
            raise RuntimeError(result.stderr)
        values = [float(line) for line in result.stdout.splitlines()]
        assert len(values) == n
        return values


if __name__ == '__main__':
    # Command line: c1,c2,... L1,L2,... . Decimal output round-trips binary64.
    counts = list(map(float, sys.argv[1].split(',')))
    libraries = list(map(float, sys.argv[2].split(',')))
    for value in run(counts, libraries):
        print(format(value, '.17g'))
