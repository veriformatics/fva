#!/usr/bin/env python3
"""Pin the shipped bytes and replay the exact binary64 counterexample."""
from fractions import Fraction
from pathlib import Path
import hashlib
import struct
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent
EXPECTED_BYTES = bytes.fromhex(
    "0061736d0100000001060160017c017f030201000503010001071302066d656d"
    "6f727902000669726f756e6400000a12011000200044000000000000e03fa0fc020b"
)
EXPECTED_SHA256 = "eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a"


def require(condition, message):
    if not condition:
        raise SystemExit("FAIL: " + message)


def run(*args):
    return subprocess.run(args, check=True, text=True, capture_output=True)


def main():
    artifact = ROOT / "glm-iround.wasm"
    raw = artifact.read_bytes()
    require(raw == EXPECTED_BYTES, "artifact bytes changed")
    require(hashlib.sha256(raw).hexdigest() == EXPECTED_SHA256, "digest mismatch")
    run("wasm-tools", "validate", str(artifact))

    bits = 0x3FDFFFFFFFFFFFFF
    x = Fraction.from_float(struct.unpack(">d", bits.to_bytes(8, "big"))[0])
    require(x == Fraction(9007199254740991, 18014398509481984), "input decode mismatch")
    require(0 <= x <= 2147483647, "input outside R1 domain")
    require(abs(x) < abs(x - 1), "1 is not strictly worse than 0")

    with tempfile.TemporaryDirectory(prefix="iround-verification-") as directory:
        wrapper = Path(directory) / "counterexample.wasm"
        run("wasm-tools", "parse", str(ROOT / "counterexample.wat"), "-o", str(wrapper))
        result = run("wasmtime", "run", "-C", "cache=n", "--preload", f"artifact={artifact}",
                     "--invoke", "counterexample", str(wrapper))
    require(result.stdout.strip() == "1", "artifact did not return 1: " + result.stdout)

    print(f"PASS: exact artifact ({len(raw)} bytes), sha256 {EXPECTED_SHA256}")
    print(f"PASS: input bits 0x{bits:016x}, exact value {x}")
    print("PASS: shipped iround returns 1; integer 0 is strictly closer. R1 FAILS.")


if __name__ == "__main__":
    main()
