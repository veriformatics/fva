#!/usr/bin/env python3
"""Replay Lean's exact cases against the original binary in Wasmtime.

This is a cross-check of execution semantics, not an all-input proof or a check
of read confinement (ordinary Wasmtime does not expose a memory-access trace).
"""
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def quoted(data):
    return '"' + ''.join(f'\\{b:02x}' for b in data) + '"'


def eq_byte(address, expected, error):
    return (f"i32.const {address}\ni32.load8_u\ni32.const {expected}\ni32.ne\n"
            f"if\ni32.const {error}\nreturn\nend\n")


def wast(cases):
    data = (ROOT / "lz4-flex.wasm").read_bytes()
    parts = [f"(module $artifact binary {quoted(data)})\n",
             '(register "artifact" $artifact)\n',
             '(module $harness\n',
             '(import "artifact" "memory" (memory 32 32))\n',
             '(import "artifact" "lz4_decompress" '
             '(func $decode (param i32 i32 i32 i32) (result i32)))\n']
    for i, c in enumerate(cases):
        src, dst, cap = c['src'], c['dst'], c['cap']
        n = len(c['input'])
        parts.append(f"(data $input{i} {quoted(c['input'])})\n")
        parts.append(f'(func (export "case{i}") (result i32)\n')
        parts.append("i32.const 131072\ni32.const 165\ni32.const 1966080\nmemory.fill\n")
        parts.append(f"i32.const {src}\ni32.const 0\ni32.const {n}\nmemory.init $input{i}\n")
        parts.append(f"i32.const {src}\ni32.const {dst}\ni32.const {n}\ni32.const {cap}\ncall $decode\n")
        signed = c['returnWord']
        if signed >= 2**31:
            signed -= 2**32
        parts.append(f"i32.const {signed}\ni32.ne\nif\ni32.const 1\nreturn\nend\n")
        for j, b in enumerate(c['output']):
            parts.append(eq_byte(dst+j, b, 2))
        for j, b in enumerate(c['input']):
            parts.append(eq_byte(src+j, b, 3))
        for p in sorted({src-1, src+n, dst-1, dst+cap, 131072, 2097151}):
            if (131072 <= p < 2097152 and not src <= p < src+n
                    and not dst <= p < dst+cap):
                parts.append(eq_byte(p, 165, 4))
        parts.append("i32.const 0\n)\n")
    parts.append(")\n")
    for i, c in enumerate(cases):
        parts.append(f';; {c["name"]}: src={c["src"]}, dst={c["dst"]}, cap={c["cap"]}\n')
        parts.append(f'(assert_return (invoke $harness "case{i}") (i32.const 0))\n')
    return ''.join(parts)


def main():
    result = subprocess.run(['lake', 'env', 'lean', '--run', 'verification/Export.lean'],
                            cwd=ROOT, check=True, text=True, capture_output=True)
    cases = json.loads(result.stdout)
    with tempfile.TemporaryDirectory(prefix='lz4-verification-') as tmp:
        script = Path(tmp) / 'replay.wast'
        script.write_text(wast(cases))
        subprocess.run(['wasmtime', 'wast', '-C', 'cache=n', str(script)], cwd=ROOT, check=True)
    print(f"PASS: {len(cases)} original-artifact Wasmtime replays (returns, output, source, canaries)")


if __name__ == '__main__':
    main()
