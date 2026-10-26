#!/usr/bin/env python3
"""Run the unchanged edgeR.so with a small, explicit Wasm host in Wasmtime."""
import hashlib
from pathlib import Path
import re
import struct
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
ARTIFACT = ROOT / "edgeR.so"
SHA256 = "e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb"
SOURCES = {
    "R/cpm.R": "b43ab97191a448ef8d141decdef802be3329801692a9c9a0618cf5ef874eb39b",
    "R/filterByExpr.R": "abd43b83d5742dd789fb501ec49d073c690000e23d09604c4d085165a6c92f5f",
}


def bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def script(cases):
    assert 0 < len(cases) <= 256
    binary = ARTIFACT.read_bytes()
    assert len(binary) == 96558 and hashlib.sha256(binary).hexdigest() == SHA256
    for path, digest in SOURCES.items():
        assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest, path
    text = subprocess.check_output(["wasm-tools", "print", str(ARTIFACT)], text=True)
    modules = {name: [] for name in ("env", "GOT.mem", "GOT.func")}
    for line in text.splitlines():
        match = re.fullmatch(r'  \(import "([^"]+)" "([^"]+)" (.*)\)', line)
        if not match:
            continue
        module, name, desc = match.groups()
        if desc.startswith("(func"):
            signature = " ".join(re.findall(r'\((?:param|result) [^)]*\)', desc))
            if name == "R_chk_calloc":
                body = """(local $p i32)
                  global.get $heap local.tee $p
                  local.get 0 local.get 1 i32.mul i32.add
                  i32.const 7 i32.add i32.const -8 i32.and global.set $heap
                  local.get $p i32.const 0 local.get 0 local.get 1 i32.mul memory.fill
                  local.get $p"""
            elif name == "R_chk_free":
                body = ""  # Retain allocations until the test process ends.
            elif name in ("__cxa_atexit", "pthread_mutex_init", "pthread_mutex_destroy"):
                body = "i32.const 0"  # Constructors only: registration/single-thread locks.
            else:
                body = "unreachable"  # An unexpected dependency fails the test.
            definition = f'(func (export "{name}") {signature} {body})'
        elif desc.startswith("(global"):
            mutable = "(mut i32)" in desc
            value = 120000 if name == "__stack_pointer" else 0
            definition = f'(global (export "{name}") {"(mut i32)" if mutable else "i32"} (i32.const {value}))'
        elif desc.startswith("(memory"):
            definition = '(memory (export "memory") 2)'
        elif desc.startswith("(table"):
            definition = '(table (export "__indirect_function_table") 9 funcref)'
        else:
            raise AssertionError(desc)
        modules[module].append(definition)
    output = []
    for index, (name, definitions) in enumerate(modules.items()):
        extra = '(global $heap (mut i32) (i32.const 32768))' if name == "env" else ""
        output.append(f'(module $host{index} {extra}\n' + "\n".join(definitions) + ")")
        output.append(f'(register "{name}" $host{index})')
    # Embed the original binary, including all custom sections, without re-encoding it.
    escaped = "".join(f"\\{b:02x}" for b in binary)
    output += [f'(module $edgeR binary "{escaped}")', '(register "edgeR" $edgeR)']
    output += ['(invoke $edgeR "__wasm_apply_data_relocs")', '(invoke $edgeR "__wasm_call_ctors")']
    count_base, library_base, out_base = 25600, 25600 + 8 * len(cases), 25600 + 16 * len(cases)
    stores = []
    for i, (count, library, _) in enumerate(cases):
        for base, value in ((count_base, count), (library_base, library), (out_base, count)):
            stores.append(f'(f64.store (i32.const {base + 8*i}) (f64.const {value.hex()}))')
    output.append(f'''(module $test
      (import "env" "memory" (memory 2))
      (import "edgeR" "calc_cpm_raw" (func $raw (param i32 i32 i32 i32)))
      (import "edgeR" "make_cmx" (func $make (param i32 i32 i32 i32 i32 i32 i32)))
      (func (export "run")
        {" ".join(stores)}
        (call $make (i32.const 24576) (i32.const {count_base}) (i32.const 0)
          (i32.const 1) (i32.const {len(cases)}) (i32.const 0) (i32.const 0))
        (call $make (i32.const 24608) (i32.const {library_base}) (i32.const 0)
          (i32.const 1) (i32.const {len(cases)}) (i32.const 0) (i32.const 0))
        (call $raw (i32.const 24576) (i32.const 24608) (i32.const {out_base}) (i32.const 1)))
      (func (export "bits") (param $i i32) (result i64)
        (i64.reinterpret_f64 (f64.load
          (i32.add (i32.const {out_base}) (i32.mul (local.get $i) (i32.const 8)))))))''')
    output.append('(invoke $test "run")')
    for i, (_, _, expected) in enumerate(cases):
        output.append(f'(assert_return (invoke $test "bits" (i32.const {i})) (i64.const {bits(expected)}))')
    return "\n".join(output) + "\n"


def check(cases):
    with tempfile.TemporaryDirectory(prefix="edger-verification-") as tmp:
        wast = Path(tmp) / "counterexamples.wast"
        wast.write_text(script(cases))
        subprocess.run(["wasmtime", "wast", "-C", "cache=n", str(wast)], check=True)


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--check-cpm":
        # R sends exact binary64 c, L, expected triples, all little-endian.
        data = Path(sys.argv[2]).read_bytes()
        assert len(data) % 24 == 0
        check(list(struct.iter_unpack("<ddd", data)))
    else:
        assert len(sys.argv) == 1
        large = float.fromhex("0x1p+1023")
        cases = [(large, large, float("inf")), (10., 1e6, 10.),
                 (10., 18., 10. * 1e6 / 18.), (20., 18., 20. * 1e6 / 18.)]
        check(cases)
        assert large / large * 1e6 == 1e6
        assert 10. * 1e6 / 18. < 10. / 18. * 1e6
        print(f"Artifact SHA256: {SHA256}")
        print("R1: c = L = 2^1023: artifact returns +infinity; c/L*10^6 = 1000000 exactly.")
        print("R2 rounding: c=10, L=18: artifact CPM bits = " + hex(bits(cases[2][2])))
        print("All unchanged-artifact Wasmtime assertions passed.")
