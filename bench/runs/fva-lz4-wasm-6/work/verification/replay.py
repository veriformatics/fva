#!/usr/bin/env python3
"""Replay counterexamples against the unchanged shipped Wasm, using wasmtime."""
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
ARTIFACT = ROOT / "lz4-block-codec.wasm"
EXPECTED_HASH = "4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf"
assert hashlib.sha256(ARTIFACT.read_bytes()).hexdigest() == EXPECTED_HASH
subprocess.run(["wasm-tools", "validate", str(ARTIFACT)], check=True)

IMPORTS = '''(module
(import "codec" "memory" (memory 1))
(import "codec" "lz4BlockEncode" (func $enc (param i32 i32 i32) (result i32)))
(import "codec" "lz4BlockDecode" (func $dec (param i32 i32 i32) (result i32)))
'''


def check_memory(address, expected):
    """WAT: combine the current boolean with byte comparisons."""
    return "\n".join(
        f"i32.const {address+i} i32.load8_u i32.const {b} i32.eq i32.and"
        for i, b in enumerate(expected)
    )


with tempfile.TemporaryDirectory(prefix="lz4-replay-") as directory:
    directory = Path(directory)
    env = dict(os.environ, XDG_CACHE_HOME=str(directory / "cache"))

    def run(name, setup, body, trap=False):
        source = directory / f"{name}.wat"
        binary = source.with_suffix(".wasm")
        source.write_text(IMPORTS + setup + '\n(func (export "test") (result i32) '
                          + body + '))\n')
        subprocess.run(["wasm-tools", "parse", str(source), "-o", str(binary)], check=True)
        result = subprocess.run(
            ["wasmtime", "run", "--preload", f"codec={ARTIFACT}",
             "--invoke", "test", str(binary)],
            capture_output=True, text=True, env=env,
        )
        if trap:
            assert result.returncode != 0 and "out of bounds memory access" in result.stderr, result
            assert "0x10000" in result.stderr, result.stderr
        else:
            assert result.returncode == 0 and result.stdout.strip() == "1", result
        print(f"{name}: counterexample confirmed")

    run("R1", '''
(data $input "abcdeabcdWXYZ")
(func $init (local $p i32)
  i32.const 4 memory.grow drop
  i32.const 262144 i32.const 0 i32.const 13 memory.init $input
  loop $fill
    local.get $p i32.const -65536 i32.store
    local.get $p i32.const 4 i32.add local.tee $p
    i32.const 262144 i32.lt_u br_if $fill
  end)
(start $init)
''', "i32.const 262144 i32.const 13 i32.const 262200 call $enc i32.const 13 i32.eq\n"
        + check_memory(262200, [80,97,98,99,100,101,5,0,64,87,88,89,90]))

    run("R2", '(data (i32.const 100) "\\10A\\01\\00\\80BCDEFGHI")',
        "i32.const 100 i32.const 13 i32.const 0 call $dec i32.const 1 i32.eq\n"
        + check_memory(0, [65] + [0]*12))

    run("R3-boundary", '(data (i32.const 65535) "\\00")',
        "i32.const 65535 i32.const 1 i32.const 0 call $dec", trap=True)

    for outside_byte, returned in [(0, 0), (1, 4)]:
        run(f"R3-outside-byte-{outside_byte}",
            f'(data (i32.const 100) "\\00\\{outside_byte:02x}\\00")',
            "i32.const 100 i32.const 1 i32.const 1000 call $dec "
            f"i32.const {returned} i32.eq\n" + check_memory(1000, [0]*4))

print("All counterexamples reproduced on the pinned artifact.")
