#!/usr/bin/env python3
"""Check an exact-input counterexample by executing the shipped Wasm bytes."""
from fractions import Fraction
from pathlib import Path
import hashlib
import math
import struct
import subprocess
import tempfile


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


root = Path(__file__).resolve().parent
artifact = (root / "glm-iround.wasm").read_bytes()
expected_hash = "eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a"
require(len(artifact) == 66, "artifact size mismatch")
require(hashlib.sha256(artifact).hexdigest() == expected_hash, "artifact hash mismatch")
# Literal byte equality also pins the module without depending on hash uniqueness.
require(artifact.hex() == (
    "0061736d0100000001060160017c017f030201000503010001"
    "071302066d656d6f727902000669726f756e640000"
    "0a12011000200044000000000000e03fa0fc020b"
), "artifact byte mismatch")

decimal = "0.499999999999999944488848768742172978818416595458984375"
x = Fraction(9007199254740991, 18014398509481984)
require(Fraction(decimal) == x, "decimal is not the exact witness")
f64 = float(decimal)
require(math.isfinite(f64), "input is not finite")
require(struct.pack(">d", f64).hex() == "3fdfffffffffffff", "input bits mismatch")
require(Fraction.from_float(f64) == x, "binary64 value mismatch")
require(0 <= x <= 2147483647, "input outside R1 domain")

# Execute a snapshot of the very bytes checked above; avoid a second read of
# the artifact and disable Wasmtime's cache so this works in the sandbox.
with tempfile.TemporaryDirectory(prefix="iround-check-") as directory:
    snapshot = Path(directory) / "glm-iround.wasm"
    snapshot.write_bytes(artifact)
    subprocess.run(["wasm-tools", "validate", str(snapshot)], check=True)
    result = subprocess.run(
        ["wasmtime", "run", "-C", "cache=n", "--invoke", "iround", str(snapshot), decimal],
        check=True, text=True, capture_output=True,
    )
require(result.stdout.strip() == "1", "unexpected iround output: " + result.stdout)
returned = int(result.stdout.strip())
require(abs(x - 0) < abs(x - returned), "returned result has no closer competitor")
print("PASS: exact 66 artifact bytes match README; Wasm validates")
print("PASS: finite binary64 input bits = 0x3fdfffffffffffff")
print(f"PASS: x = {x}; iround(x) = {returned}")
print(f"PASS: distance to 0 = {abs(x)} < distance to 1 = {abs(x - 1)}")
print("R1 FAILS: returned integer 1 is strictly farther away than integer 0")
