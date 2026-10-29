#!/usr/bin/env python3
"""Replay R1's counterexample against the exact shipped WebAssembly bytes."""
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent
EXPECTED = bytes.fromhex(
    "0061736d0100000001060160017c017f030201000503010001071302066d656d6f7279"
    "02000669726f756e6400000a12011000200044000000000000e03fa0fc020b"
)
DIGEST = "eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def run(*args):
    return subprocess.run(
        args, cwd=ROOT, check=True, capture_output=True, text=True
    ).stdout.strip()


artifact = (ROOT / "glm-iround.wasm").read_bytes()
require(artifact == EXPECTED, "artifact bytes differ from the checked artifact")
require(len(artifact) == 66 and sha256(artifact).hexdigest() == DIGEST,
        "artifact size or SHA-256 mismatch")
run("wasm-tools", "validate", "glm-iround.wasm")

# The harness supplies these bits with f64.reinterpret_i64, without decimal parsing.
bits = 0x3FDFFFFFFFFFFFFF
sign = bits >> 63
exponent = (bits >> 52) & 0x7FF
fraction = bits & ((1 << 52) - 1)
require(sign == 0 and exponent == 1021 and fraction == (1 << 52) - 1,
        "unexpected IEEE-754 fields")
require(0 < exponent < 2047, "input must be finite and normal")
x = (1 + Fraction(fraction, 1 << 52)) / 4
require(x == Fraction(9007199254740991, 18014398509481984),
        "input differs from IRound.x in Lean")
require(0 <= x <= 2147483647, "input outside R1's domain")

observed = run("wasmtime", "run", "-C", "cache=n", "--preload",
               "artifact=glm-iround.wasm", "--invoke", "observed",
               "counterexample.wat")
require(observed == "1", f"expected result 1, got {observed!r}")
require(abs(x) < abs(x - int(observed)), "no strict nearest-integer violation")
print(f"Artifact: 66 bytes, SHA-256 {DIGEST}")
print(f"Input: 0x{bits:016x} = {x}")
print(f"Observed iround result: {observed}; integer 0 is strictly closer.")
print("PASS: R1 is FALSE for the shipped artifact.")
