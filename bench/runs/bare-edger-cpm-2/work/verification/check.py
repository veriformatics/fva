#!/usr/bin/env python3
"""Replay counterexamples against pinned, unchanged shipped bytes. No network."""
import hashlib
import os
from pathlib import Path
import re
import struct
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def run(*args):
    result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(f'{args}:\n{result.stdout}\n{result.stderr}')
    return result.stdout.strip()


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def bits(value):
    return struct.unpack('<Q', struct.pack('<d', value))[0]


def environment(wat):
    """Supply imports; every function except zeroed allocation/free traps if called."""
    out = ['(module $env', '  (global $heap (mut i32) (i32.const 262144))']
    imports = re.findall(r'^  \(import "([^"]+)" "([^"]+)" (.*)\)$', wat, re.M)
    require(len(imports) == 151, 'Unexpected artifact import set')
    names = set()
    for module, name, desc in imports:
        require(module in ('env', 'GOT.mem', 'GOT.func'), 'Unexpected import module')
        require(name not in names, 'Duplicate import export name')
        names.add(name)
        export = f'(export "{name}")'
        if desc.startswith('(func '):
            sig = ' '.join(re.findall(r'\((?:param|result) [^)]*\)', desc))
            body = 'unreachable'
            if name == 'R_chk_calloc':
                body = '''(local $p i32) (local $n i32)
                  (local.set $p (global.get $heap))
                  (local.set $n (i32.mul (local.get 0) (local.get 1)))
                  (global.set $heap (i32.and
                    (i32.add (i32.add (global.get $heap) (local.get $n)) (i32.const 7))
                    (i32.const -8)))
                  (memory.fill (local.get $p) (i32.const 0) (local.get $n))
                  (local.get $p)'''
            elif name == 'R_chk_free':
                body = ''  # valid short-lived host allocator: never reuses a freed block
            out.append(f'  (func {export} {sig} {body})')
        elif desc.startswith('(global '):
            ty = '(mut i32)' if '(mut i32)' in desc else 'i32'
            value = 131072 if name == '__stack_pointer' else 0
            out.append(f'  (global {export} {ty} (i32.const {value}))')
        elif desc.startswith('(memory '):
            out.append(f'  (memory {export} 32)')
        elif desc.startswith('(table '):
            out.append(f'  (table {export} 9 funcref)')
        else:
            raise AssertionError(f'Unknown import: {desc}')
    out.append(')')
    return '\n'.join(out)


def main():
    for line in (ROOT / 'verification/inputs.sha256').read_text().splitlines():
        digest, name = line.split('  ', 1)
        data = (ROOT / name).read_bytes()
        require(hashlib.sha256(data).hexdigest() == digest, f'Changed input: {name}')
    original = (ROOT / 'edgeR.so').read_bytes()
    require(len(original) == 96558, 'Artifact length mismatch')
    require(hashlib.sha256(original).hexdigest() ==
            'e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb',
            'Artifact SHA-256 mismatch')
    print('Pinned input hashes: PASS', flush=True)
    run('wasm-tools', 'validate', 'edgeR.so')
    wat = run('wasm-tools', 'print', 'edgeR.so')
    env = environment(wat)
    probe = (ROOT / 'verification/probe.wat').read_text()
    with tempfile.TemporaryDirectory(prefix='edger-verification-') as tmp:
        tmp = Path(tmp)
        os.environ["XDG_CACHE_HOME"] = str(tmp / "cache")
        (tmp / 'env.wat').write_text(env)
        run('wasm-tools', 'parse', str(tmp / 'env.wat'), '-o', str(tmp / 'env.wasm'))
        run('wasm-tools', 'parse', 'verification/probe.wat', '-o', str(tmp / 'probe.wasm'))
        # Embed the exact original binary. No editing, slicing, or recompiling it.
        binary = ''.join(f'\\{byte:02x}' for byte in original)
        wast = env + '\n' + '\n'.join(
            f'(register "{name}" $env)' for name in ('env', 'GOT.mem', 'GOT.func'))
        wast += f'\n(module $edge binary "{binary}")\n(register "edge" $edge)\n' + probe
        wast += '''
(assert_return (invoke $probe "scalar" (f64.const 10) (f64.const 18))
  (f64.const 0x1.0f4471c71c71cp+19))
(assert_return (invoke $probe "scalar" (f64.const 0x1p+1023) (f64.const 0x1p+1023))
  (f64.const inf))
(assert_return (invoke $probe "divide_first" (f64.const 0x1p+1023) (f64.const 0x1p+1023))
  (f64.const 1000000))
(assert_return (invoke $probe "scalar" (f64.const 10) (f64.const 1000000))
  (f64.const 10))
(assert_return (invoke $probe "matrix_cell" (i32.const 0))
  (f64.const 0x1.0f4471c71c71cp+19))
(assert_return (invoke $probe "matrix_cell" (i32.const 1))
  (f64.const 0x1.b2071c71c71c7p+18))
(assert_return (invoke $probe "matrix_cell" (i32.const 2))
  (f64.const 0x1.0f4471c71c71cp+19))
(assert_return (invoke $probe "matrix_cell" (i32.const 3))
  (f64.const 0x1.b2071c71c71c7p+18))
'''
        (tmp / 'counterexamples.wast').write_text(wast)
        run('wasmtime', 'wast', str(tmp / 'counterexamples.wast'))
        print('Original-byte Wasmtime assertions: PASS (R1 overflow and R2 boundary)', flush=True)
        print('R1: c=L=0x1p+1023; kernel=+inf; divide-first=1000000', flush=True)
        prefix = ['wasmtime', '--preload', f'env={tmp / "env.wasm"}',
                  '--preload', f'GOT.mem={tmp / "env.wasm"}',
                  '--preload', f'GOT.func={tmp / "env.wasm"}',
                  '--preload', f'edge={ROOT / "edgeR.so"}']
        values = []
        for i in range(4):
            value = float(run(*prefix, '--invoke', 'matrix_cell', str(tmp / 'probe.wasm'), str(i)))
            require(bits(value) == (0x4120f4471c71c71c if i % 2 == 0 else 0x411b2071c71c71c7),
                    'CLI transport changed output bits')
            values.append(format(value, '.17g'))
        csv = tmp / 'cpm.txt'
        csv.write_text('\n'.join(values) + '\n')
        print(run('Rscript', '--vanilla', 'verification/filter.R', str(csv)), flush=True)
    print('All executable counterexamples: PASS', flush=True)


if __name__ == '__main__':
    main()
