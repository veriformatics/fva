#!/usr/bin/env python3
"""Execute the unchanged edgeR.so, supplying only memory and allocation services."""
import hashlib
import pathlib
import re
import struct
import subprocess
import tempfile
from fractions import Fraction

ROOT = pathlib.Path(__file__).resolve().parent.parent
SHA256 = "e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb"
INPUT_HASHES = {
    "README.md": "fd3bfde0f91942014be02782a759b571a795b81499f5536bc8b5e0168d324a3b",
    "R/cpm.R": "b43ab97191a448ef8d141decdef802be3329801692a9c9a0618cf5ef874eb39b",
    "R/filterByExpr.R": "abd43b83d5742dd789fb501ec49d073c690000e23d09604c4d085165a6c92f5f",
    "man/filterByExpr.Rd": "45cef156e3cd3163cb7e20276d921a57715e71c27beb2487f6514b789c21c98a",
    "src/edgeR.h": "dc7a390cb5c1e026fc2dc7f9227cf56810961d41d54ad6ce6b93df3a80f9c219",
    "src/compute_cpm.c": "1291d75055e18299a436c4474225f5d1f73556a7ddb149a0b6c94f9e20d723fd",
}


def run(*args):
    result = subprocess.run(args, cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode:
        raise RuntimeError(f"{args[0]} failed:\n{result.stdout}{result.stderr}")
    return result.stdout


def host_modules(wat, directory):
    """Read import signatures; all services except calloc/free trap if called."""
    types = {}
    for line in wat.splitlines():
        m = re.fullmatch(r"  \(type \(;([0-9]+);\) \(func(.*)\)\)", line)
        if m:
            types[m[1]] = m[2]
    modules = {name: [] for name in ("env", "GOT.mem", "GOT.func")}
    for line in wat.splitlines():
        m = re.fullmatch(r'  \(import "([^"]+)" "([^"]+)" (.*)\)', line)
        if not m:
            continue
        module, name, desc = m.groups()
        assert module in modules, (module, name)
        export = f'(export "{name}")'
        if desc.startswith("(func"):
            signature = types[re.search(r"\(type ([0-9]+)\)", desc)[1]]
            if name == "R_chk_calloc":
                assert signature == " (param i32 i32) (result i32)"
                # Positive, tiny test allocations; non-overlapping, zeroed,
                # 8-byte aligned blocks in the imported memory. No reuse.
                body = """(local $p i32) (local $n i32)
                  local.get 0 local.get 1 i32.mul local.set $n
                  global.get $heap local.set $p
                  local.get $p local.get $n i32.add i32.const 7 i32.add
                  i32.const -8 i32.and global.set $heap
                  global.get $heap i32.const 2000000 i32.gt_u if unreachable end
                  local.get $p i32.const 0 local.get $n memory.fill
                  local.get $p"""
            elif name == "R_chk_free":
                assert signature == " (param i32)"
                body = ""  # Fresh instance per call, so no reclamation is needed.
            else:
                body = "unreachable"
            modules[module].append(f"(func {export}{signature} {body})")
        elif desc.startswith("(global"):
            ty = "(mut i32)" if "(mut i32)" in desc else "i32"
            value = {"__stack_pointer": 524288, "__memory_base": 4096,
                     "__table_base": 0}.get(name, 0)
            modules[module].append(f"(global {export} {ty} (i32.const {value}))")
        elif desc.startswith("(memory"):
            modules[module].append(f"(memory {export} 32)")
        elif desc.startswith("(table"):
            modules[module].append(f"(table {export} 1024 funcref)")
        else:
            raise AssertionError(desc)
    modules["env"].append("(global $heap (mut i32) (i32.const 1048576))")
    for name, declarations in modules.items():
        path = directory / (name + ".wat")
        path.write_text("(module\n" + "\n".join(declarations) + "\n)\n")
        run("wasm-tools", "parse", str(path), "-o", str(path.with_suffix(".wasm")))


def harness(directory):
    parts = ['(module (import "env" "memory" (memory 32))',
             '(import "edgeR" "calc_cpm_raw" (func $calc (param i32 i32 i32 i32)))']
    cases = {"overflow": (1, [float.fromhex("0x1p+1023")],
                          [float.fromhex("0x1p+1023")]),
             "boundary": (2, [10., 26., 10., 26.], [36., 36.]),
             "tolerance": (1, [20., 0.], [1e6, 1e6])}
    for name, (nrow, counts, libs) in cases.items():
        ncol = len(libs)
        setup = []
        def put_i32(addr, value):
            setup.append(f"i32.const {addr} i32.const {value} i32.store")
        def put_f64(addr, value):
            setup.append(f"i32.const {addr} f64.const {value.hex()} f64.store")
        # wasm32 cmx, layout documented in src/edgeR.h (eight 32-bit fields).
        for base, data, ty in [(65536, 65800, 0), (65600, 65700, 2)]:
            for offset, value in enumerate([data, 0, nrow, ncol, ty, 0, nrow, 0]):
                put_i32(base + 4 * offset, value)
        for i, value in enumerate(libs):
            put_f64(65700 + 8 * i, value)
        for i, value in enumerate(counts):
            put_f64(65800 + 8 * i, value)
        setup.append("i32.const 65536 i32.const 65600 i32.const 65800 i32.const 1 call $calc")
        parts.append(f'(func ${name}\n' + '\n'.join(setup) + ')')
        for i in range(len(counts)):
            parts.append(f'(func (export "{name}{i}") (result i64) call ${name} '
                         f'i32.const {65800 + 8*i} i64.load)')
    path = directory / "harness.wat"
    path.write_text("\n".join(parts) + ")\n")
    run("wasm-tools", "parse", str(path), "-o", str(directory / "harness.wasm"))
    return cases


def main():
    artifact = ROOT / "edgeR.so"
    assert artifact.stat().st_size == 96558
    assert hashlib.sha256(artifact.read_bytes()).hexdigest() == SHA256
    for name, digest in INPUT_HASHES.items():
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, name
    run("wasm-tools", "validate", str(artifact))
    wat = run("wasm-tools", "print", str(artifact))
    assert '(export "calc_cpm_raw" (func 160))' in wat
    with tempfile.TemporaryDirectory(prefix="edger-verification-") as tmp:
        directory = pathlib.Path(tmp)
        host_modules(wat, directory)
        cases = harness(directory)
        command = ["wasmtime", "-C", "cache=n"]
        for module in ("env", "GOT.mem", "GOT.func"):
            command += ["--preload", f"{module}={directory / (module + '.wasm')}"]
        # This preload is the original, hash-checked binary, without modification.
        command += ["--preload", f"edgeR={artifact}"]
        results = {}
        for name, (_, counts, _) in cases.items():
            bits = []
            for i in range(len(counts)):
                output = run(*command, "--invoke", f"{name}{i}",
                             str(directory / "harness.wasm"))
                bits.append(int(output.strip()) % (1 << 64))
            values = [struct.unpack("<d", struct.pack("<Q", b))[0] for b in bits]
            results[name] = values
            (directory / (name + ".bin")).write_bytes(struct.pack("<" + "Q"*len(bits), *bits))
            print(name + " result bits: " + " ".join(f"{b:016x}" for b in bits))
        assert results["overflow"] == [float("inf")]
        c = Fraction(2)**1023
        assert c / c * 1000000 == 1000000
        print("R1 FAIL witness checked: finite c=L=2^1023; exact CPM=1000000; artifact=+infinity")
        actual = Fraction.from_float(results["boundary"][0])
        assert actual == Fraction(1193046471111111, 4294967296)
        assert actual - Fraction(10000000, 36) == -Fraction(1, 38654705664)
        assert results["tolerance"] == [20., 0.]
        print(run("Rscript", "--vanilla", "Verification/check_filter.R", str(directory)), end="")
    print("PASS: all counterexample checks completed")


if __name__ == "__main__":
    main()
