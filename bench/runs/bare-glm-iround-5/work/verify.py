#!/usr/bin/env python3
"""Check the shipped bytes, execute the witness, and kernel-check its arithmetic."""
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import subprocess
import tempfile


def require(condition, message):
    if not condition:
        raise SystemExit("FAIL: " + message)


def run(*args):
    result = subprocess.run(args, text=True, capture_output=True)
    require(result.returncode == 0,
            f"{args!r} exited {result.returncode}\n{result.stdout}{result.stderr}")
    return result.stdout.strip()


root = Path(__file__).resolve().parent
require(Path.cwd() == root, "run this script from the project directory")
artifact = (root / "glm-iround.wasm").read_bytes()
expected = bytes.fromhex(
    "0061736d0100000001060160017c017f"
    "030201000503010001071302066d656d"
    "6f727902000669726f756e6400000a12"
    "011000200044000000000000e03fa0fc020b"
)
require(artifact == expected, "artifact differs from the reviewed 66 bytes")
digest = sha256(artifact).hexdigest()
require(digest == "eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a",
        "artifact digest differs from README")
print(f"PASS: exact {len(artifact)} artifact bytes; sha256 {digest}", flush=True)

# A snapshot ensures the actual invocation uses the bytes just checked.
with tempfile.TemporaryDirectory(prefix="iround-verification-") as temporary:
    snapshot = Path(temporary) / "shipped.wasm"
    harness = Path(temporary) / "witness.wasm"
    snapshot.write_bytes(artifact)
    run("wasm-tools", "validate", str(snapshot))
    run("wasm-tools", "parse", "witness.wat", "-o", str(harness))
    run("wasm-tools", "validate", str(harness))
    output = run("wasmtime", "run", "-C", "cache=n", "--preload",
                 f"shipped={snapshot}", "--invoke", "run", str(harness))
    require(output == "1", f"expected observed result 1, received {output!r}")
print("PASS: actual artifact returns i32 1 for f64 bits 0x3fdfffffffffffff", flush=True)

# Independent exact arithmetic; the Lean proof below checks the same claims.
bits = 0x3fdfffffffffffff
sign, exponent, fraction = bits >> 63, (bits >> 52) & 2047, bits & ((1 << 52) - 1)
require(sign == 0 and 0 < exponent < 2047, "input must be finite positive normal")
x = (1 + Fraction(fraction, 1 << 52)) * Fraction(2) ** (exponent - 1023)
require(x == Fraction(1, 2) - Fraction(1, 1 << 54), "input decoding mismatch")
require(0 <= x <= 2147483647, "input outside R1 domain")
require(abs(x) < abs(x - 1), "zero is not strictly closer than the observed result")
print(f"PASS: exact x = {x}; distance to 0 < distance to 1", flush=True)

# Direct elaboration checks proofs even if Lake build outputs already exist.
print(run("lake", "env", "lean", "Proofs/Counterexample.lean"), flush=True)
print("PASS: Lean checked the certificate; R1 is FALSE", flush=True)
