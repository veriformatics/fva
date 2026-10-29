#!/usr/bin/env python3
"""Check the shipped bytes and run an exact-literal Wasmtime counterexample."""
from fractions import Fraction
import hashlib
from pathlib import Path
import subprocess
import tempfile


def check(condition, message):
    if not condition:
        raise RuntimeError(message)


root = Path(__file__).resolve().parent
artifact = (root / "glm-iround.wasm").read_bytes()
expected = bytes.fromhex(
    "0061736d0100000001060160017c017f030201000503010001071302066d"
    "656d6f727902000669726f756e6400000a12011000200044000000000000"
    "e03fa0fc020b"
)
check(artifact == expected, "artifact bytes differ from the reviewed 66-byte module")
digest = hashlib.sha256(artifact).hexdigest()
check(digest == "eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a",
      "artifact digest differs from README")

# Decode the normal binary64 value using exact rational arithmetic.
bits = 0x3FDFFFFFFFFFFFFF
sign = bits >> 63
exponent = (bits >> 52) & 0x7FF
fraction = bits & ((1 << 52) - 1)
check((sign, exponent, fraction) == (0, 1021, 4503599627370495),
      "unexpected binary64 fields")
check(0 < exponent < 2047, "input is not finite and normal")
x = (1 + Fraction(fraction, 1 << 52)) * Fraction(2) ** (exponent - 1023)
check(x == Fraction(9007199254740991, 18014398509481984),
      "input differs from IRound.input in the Lean proof")
check(0 <= x <= 2147483647 and abs(x) < abs(x - 1),
      "counterexample arithmetic failed")

# No decimal parsing or recompilation of the target: the WAST script embeds
# the actual artifact bytes. The first assertion also checks the input bits.
escaped = "".join(f"\\{byte:02x}" for byte in artifact)
script = f'''(module $input
  (func (export "bits") (result i64)
    f64.const 0x1.fffffffffffffp-2
    i64.reinterpret_f64))
(assert_return (invoke $input "bits") (i64.const 0x3fdfffffffffffff))
(module $artifact binary "{escaped}")
(assert_return
  (invoke $artifact "iround" (f64.const 0x1.fffffffffffffp-2))
  (i32.const 1))
'''
subprocess.run(["wasm-tools", "validate", str(root / "glm-iround.wasm")], check=True)
with tempfile.TemporaryDirectory(prefix="iround-verification-") as temporary:
    wast = Path(temporary) / "counterexample.wast"
    wast.write_text(script)
    subprocess.run(["wasmtime", "wast", "-C", "cache=n", str(wast)], check=True)

print(f"PASS: exact {len(artifact)}-byte artifact, sha256 {digest}")
print("PASS: finite input bits 0x3fdfffffffffffff = 9007199254740991/18014398509481984")
print("PASS: shipped iround(input) = 1; 0 is strictly closer. R1 FAILS.")
