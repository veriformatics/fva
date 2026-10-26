#!/usr/bin/env python3
"""Execute the unmodified shipped Wasm, then run the shipped R entry points."""
import hashlib
from pathlib import Path
import re
import struct
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
HASHES = {
    "edgeR.so": "e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb",
    "R/cpm.R": "b43ab97191a448ef8d141decdef802be3329801692a9c9a0618cf5ef874eb39b",
    "R/filterByExpr.R": "abd43b83d5742dd789fb501ec49d073c690000e23d09604c4d085165a6c92f5f",
}
for name, digest in HASHES.items():
    assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, name

with tempfile.TemporaryDirectory(prefix="edger-verification-") as tmp:
    tmp = Path(tmp)
    wasm = ROOT / "edgeR.so"
    subprocess.run(["wasm-tools", "validate", str(wasm)], check=True)
    wat = subprocess.check_output(["wasm-tools", "print", str(wasm)], text=True)
    # Generate only the imports. No artifact instruction is rewritten or extracted.
    modules = {name: [] for name in ("env", "GOT.mem", "GOT.func")}
    for line in wat.splitlines():
        m = re.fullmatch(r'  \(import "([^"]+)" "([^"]+)" (.*)\)', line)
        if not m:
            continue
        mod, name, desc = m.groups()
        if desc.startswith("(func"):
            signature = " ".join(re.findall(r'\((?:param|result) [^)]*\)', desc))
            body = "unreachable"  # Unused imports must trap, never silently return.
            if name == "R_chk_calloc":
                body = """(local $p i32) (local $n i32)
                  local.get 0 local.get 1 i32.mul local.set $n
                  global.get $heap local.tee $p
                  local.get $n i32.add i32.const 7 i32.add
                  i32.const -8 i32.and global.set $heap
                  local.get $p i32.const 0 local.get $n memory.fill
                  local.get $p"""
            elif name == "R_chk_free":
                body = ""  # Fresh allocations never reuse a freed block in this run.
            modules[mod].append(f'(func (export "{name}") {signature} {body})')
        elif desc.startswith("(global"):
            mutable = "(mut i32)" in desc
            value = {"__stack_pointer": 1048576, "__memory_base": 1024}.get(name, 0)
            ty = "(mut i32)" if mutable else "i32"
            modules[mod].append(f'(global (export "{name}") {ty} (i32.const {value}))')
        elif desc.startswith("(memory"):
            modules[mod].append(f'(memory (export "{name}") 32)')
        elif desc.startswith("(table"):
            modules[mod].append(f'(table (export "{name}") 9 funcref)')
        else:
            raise AssertionError(desc)
    script = []
    for mod, definitions in modules.items():
        extra = '(global $heap (mut i32) (i32.const 200000))' if mod == "env" else ""
        script.append(f'(module ${mod} {extra}\n' + "\n".join(definitions) + ")")
        script.append(f'(register "{mod}" ${mod})')
    escaped = "".join(f"\\{b:02x}" for b in wasm.read_bytes())
    script.append(f'(module $artifact binary "{escaped}")')
    script.append('(register "artifact" $artifact)')
    script.append('''(module $test
      (import "env" "memory" (memory 32))
      (import "artifact" "calc_cpm_raw" (func $calc (param i32 i32 i32 i32)))
      ;; cmx: dmat, imat, nrow, ncol, type, isint, pnrow, rowsel (8 x i32).
      ;; Full double matrices, one row, one or two columns, no row selection.
      (func (export "run") (param $c f64) (param $L f64) (param $n i32) (result f64)
        i32.const 66000 i32.const 0 i32.const 64 memory.fill
        i32.const 66000 i32.const 67032 i32.store
        i32.const 66008 i32.const 1 i32.store
        i32.const 66012 local.get $n i32.store
        i32.const 66024 i32.const 1 i32.store
        i32.const 66032 i32.const 67064 i32.store
        i32.const 66040 i32.const 1 i32.store
        i32.const 66044 local.get $n i32.store
        i32.const 66056 i32.const 1 i32.store
        i32.const 67000 local.get $c f64.store
        i32.const 67008 local.get $c f64.store
        i32.const 67032 local.get $c f64.store
        i32.const 67040 local.get $c f64.store
        i32.const 67064 local.get $L f64.store
        i32.const 67072 local.get $L f64.store
        i32.const 66000 i32.const 66032 i32.const 67000 i32.const 1 call $calc
        i32.const 67000 f64.load)
      (func (export "second") (result f64) i32.const 67008 f64.load)
      (func (export "reference") (param f64 f64) (result f64)
        local.get 0 local.get 1 f64.div f64.const 1000000 f64.mul))''')
    script.extend([
        '(assert_return (invoke $test "run" (f64.const 0x1p+1020) (f64.const 0x1p+1020) (i32.const 1)) (f64.const inf))',
        '(assert_return (invoke $test "reference" (f64.const 0x1p+1020) (f64.const 0x1p+1020)) (f64.const 1000000))',
        '(assert_return (invoke $test "run" (f64.const 10) (f64.const 1000009) (i32.const 2)) (f64.const 0x1.3fff43420d831p+3))',
        '(assert_return (invoke $test "second") (f64.const 0x1.3fff43420d831p+3))',
        '(assert_return (invoke $test "reference" (f64.const 10) (f64.const 1000009)) (f64.const 0x1.3fff43420d832p+3))',
        '(assert_return (invoke $test "run" (f64.const 10) (f64.const 1000000) (i32.const 1)) (f64.const 10))',
    ])
    wast = tmp / "counterexamples.wast"
    wast.write_text("\n".join(script) + "\n")
    subprocess.run(["wasmtime", "wast", "-C", "cache=n", str(wast)], check=True)
    print("R1: shipped calc_cpm_raw(2^1020, 2^1020) = +inf; reference = 1000000", flush=True)
    print("Wasm: both boundary CPM entries = 0x1.3fff43420d831p+3", flush=True)
    # Values below have just been checked against both actual Wasm output cells.
    result = tmp / "boundary.bin"
    result.write_bytes(struct.pack("<QQ", 0x4023FFF43420D831, 0x4023FFF43420D831))
    subprocess.run(["Rscript", "--vanilla", str(ROOT / "verification/check.R"), str(result)], cwd=ROOT, check=True)
print("PASS: all artifact, floating-point, and R counterexample assertions")
