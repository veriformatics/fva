#!/usr/bin/env python3
"""Independent runtime checks of finite examples; not a proof of R1--R3."""
import hashlib
from pathlib import Path
import subprocess
import tempfile

CASES = [
    ("empty_zero", [0], 0, 0, []),
    ("empty_positive", [0], 1, 0, []),
    ("no_input", [], 1, -1, []),
    ("literal", [0x10, 65], 1, 1, [65]),
    ("overlap", [0x18, 65, 1, 0, 0x50, 66, 67, 68, 69, 70], 18, 18,
     [65] * 13 + [66, 67, 68, 69, 70]),
    ("literal_extension", [0xf0, 0] + list(range(65, 80)), 15, 15, list(range(65, 80))),
    ("match_extension", [0x1f, 65, 1, 0, 0, 0x50, 66, 67, 68, 69, 70], 25, 25,
     [65] * 20 + [66, 67, 68, 69, 70]),
    ("zero_offset", [8, 0, 0, 0x50, 66, 67, 68, 69, 70], 17, 17,
     [0] * 12 + [66, 67, 68, 69, 70]),
    ("bad_offset", [8, 1, 0, 0x50, 66, 67, 68, 69, 70], 17, -4, []),
    ("truncated", [0x10], 1, -2, []),
    ("too_small", [0x20, 65, 66], 1, -2, []),
    ("shortcut", [0x80] + list(range(65, 73)) + [8, 0, 0xc0] + list(range(97, 109)),
     32, 24, list(b"ABCDEFGHABCDabcdefghijkl")),
]


def check(condition):
    return f"(if (i32.eqz {condition}) (then unreachable))"


def main():
    artifact = Path("lz4-c.wasm").resolve()
    assert hashlib.sha256(artifact.read_bytes()).hexdigest() == (
        "8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6")
    with tempfile.TemporaryDirectory(prefix="lz4-examples-") as directory:
        for name, source, capacity, result, output in CASES:
            # Each subprocess instantiates the original artifact afresh. The harness
            # imports that instance's memory and function; it never rewrites its code.
            body = [f"(memory.fill (i32.const 262143) (i32.const 165) (i32.const {capacity+2}))"]
            body += [f"(i32.store8 (i32.const {131072+k}) (i32.const {b}))"
                     for k, b in enumerate(source)]
            body += [check(f"(i32.eq (call $decode (i32.const 131072) (i32.const 262144) "
                           f"(i32.const {len(source)}) (i32.const {capacity})) (i32.const {result}))")]
            for address, value in ([(262143, 165), (262144+capacity, 165)] +
                                   [(262144+k, b) for k, b in enumerate(output)] +
                                   [(131072+k, b) for k, b in enumerate(source)]):
                body += [check(f"(i32.eq (i32.load8_u (i32.const {address})) (i32.const {value}))")]
            wat = ('(module (import "lz4" "memory" (memory 32 32))\n'
                   '(import "lz4" "LZ4_decompress_safe" '
                   '(func $decode (param i32 i32 i32 i32) (result i32)))\n'
                   '(func (export "_start")\n' + '\n'.join(body) + '))\n')
            harness = Path(directory) / f"{name}.wat"
            harness.write_text(wat)
            subprocess.run(["wasmtime", "run", "-C", "cache=n", "--preload", f"lz4={artifact}",
                            str(harness)], check=True)
            print(f"PASS {name}: return {result}, output {bytes(output).hex()}", flush=True)
    print(f"PASS: {len(CASES)} finite runtime examples (not universal verification)")


if __name__ == "__main__":
    main()
