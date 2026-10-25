#!/usr/bin/env python3
"""Independent execution of the witnesses against the shipped Wasm bytes."""
import hashlib
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent.parent
artifact = root / "lz4-block-codec.wasm"
assert hashlib.sha256(artifact.read_bytes()).hexdigest() == (
    "4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf"
)
for name, expected in [("r1", "1"), ("r2", "1"), ("r3_zero", "0"), ("r3_one", "4")]:
    result = subprocess.run(
        ["wasmtime", "-C", "cache=n", "--preload", f"codec={artifact}",
         "--invoke", name, str(root / "witnesses/runtime.wat")],
        text=True, capture_output=True, check=True,
    )
    assert result.stdout.strip() == expected, (name, result.stdout, result.stderr)
    print(f"{name}: {expected} (expected)")
result = subprocess.run(
    ["wasmtime", "-C", "cache=n", "--preload", f"codec={artifact}",
     "--invoke", "boundary", str(root / "witnesses/runtime.wat")],
    text=True, capture_output=True,
)
assert result.returncode != 0, result.stdout
assert "wasm trap: out of bounds memory access" in result.stderr, result.stderr
assert "wasm address 0x10000" in result.stderr, result.stderr
print("boundary: out-of-bounds read at 65536 (expected)")
print("All artifact counterexamples reproduced.")
