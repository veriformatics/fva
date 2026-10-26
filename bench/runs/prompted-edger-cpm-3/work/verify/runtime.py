"""Run the unchanged edgeR.so through Wasmtime, with a minimal R allocation host."""
import json
from pathlib import Path
import re
import struct
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / ".verification"


def run(args):
    return subprocess.run(args, cwd=ROOT, check=True, text=True, capture_output=True).stdout


def prepare():
    OUT.mkdir(exist_ok=True)
    wat = run(["wasm-tools", "print", "edgeR.so"])
    (OUT / "edgeR.wat").write_text(wat)
    # All imported functions except the allocator/free trap if reached. Each
    # invocation has fresh zero-filled memory, and makes just one calc_cpm_raw call.
    modules = {"env": [], "GOT.mem": [], "GOT.func": []}
    for line in wat.splitlines():
        m = re.fullmatch(r'  \(import "([^"]+)" "([^"]+)" (.*)\)', line)
        if not m:
            continue
        module, name, decl = m.groups()
        if decl.startswith("(func"):
            signature = " ".join(re.findall(r"\((?:param|result) [^)]*\)", decl))
            body = "unreachable"
            if name == "R_chk_calloc":
                body = """(local $p i32)
                  global.get $heap local.set $p
                  global.get $heap local.get 0 local.get 1 i32.mul i32.add
                  i32.const 7 i32.add i32.const -8 i32.and global.set $heap
                  global.get $heap i32.const 1048576 i32.gt_u if unreachable end
                  local.get $p"""
            elif name == "R_chk_free":
                body = ""  # one-shot host: fresh instance for every result
            modules[module].append(f'(func (export "{name}") {signature} {body})')
        elif decl.startswith("(global"):
            mutable = "(mut i32)" if "(mut i32)" in decl else "i32"
            value = 2097136 if name == "__stack_pointer" else 0
            modules[module].append(f'(global (export "{name}") {mutable} (i32.const {value}))')
        elif decl.startswith("(memory"):
            modules[module].append(f'(memory (export "{name}") 32)')
        elif decl.startswith("(table"):
            modules[module].append(f'(table (export "{name}") 9 funcref)')
        else:
            raise ValueError(line)
    modules["env"].append('(global $heap (mut i32) (i32.const 131072))')
    for name, parts in modules.items():
        path = OUT / (name + ".wat")
        path.write_text("(module\n" + "\n".join(parts) + "\n)\n")
        run(["wasm-tools", "parse", str(path), "-o", str(path.with_suffix(".wasm"))])


def matrix(nrow, ncol, counts, libs):
    assert nrow > 0 and ncol > 0 and len(counts) == nrow * ncol
    assert len(libs) == ncol and all(x > 0 for x in libs)
    # cmx is {dmat, imat, nrow, ncol, type, isint, pnrow, rowsel}.
    # Both descriptors use ordinary full, double matrices (type=isint=0).
    cptr = 65600
    lptr = cptr + 8 * len(counts)
    assert lptr + 8 * len(counts) < 131072
    descriptors = struct.pack("<8I", cptr, 0, nrow, ncol, 0, 0, nrow, 0)
    descriptors += struct.pack("<8I", lptr, 0, nrow, ncol, 0, 0, nrow, 0)
    payload = descriptors + struct.pack(f"<{len(counts)}d", *counts)
    payload += struct.pack(f"<{len(counts)}d", *[v for v in libs for _ in range(nrow)])
    encoded = "".join(f"\\{b:02x}" for b in payload)
    path = OUT / "fixture.wat"
    path.write_text(f'''(module
      (import "env" "memory" (memory 32))
      (import "edgeR" "calc_cpm_raw" (func $calc (param i32 i32 i32 i32)))
      (data (i32.const 65536) "{encoded}")
      (func (export "cell") (param i32) (result i64)
        i32.const 65536 i32.const 65568 i32.const {cptr} i32.const 1 call $calc
        local.get 0 i32.const 8 i32.mul i32.const {cptr} i32.add
        f64.load i64.reinterpret_f64))
    ''')
    run(["wasm-tools", "parse", str(path), "-o", str(OUT / "fixture.wasm")])
    results = []
    for i in range(len(counts)):
        args = ["wasmtime", "run", "-C", "cache=n"]
        for name in ["env", "GOT.mem", "GOT.func"]:
            args += ["--preload", f"{name}={OUT / (name + '.wasm')}"]
        args += ["--preload", f"edgeR={ROOT / 'edgeR.so'}", "--invoke", "cell", str(OUT / "fixture.wasm"), str(i)]
        bits = int(run(args).strip()) % (1 << 64)
        results.append(struct.unpack("<d", struct.pack("<Q", bits))[0])
    return results


if __name__ == "__main__":
    # Used by the R-to-Wasm adapter; column-major counts and per-column sizes.
    request = json.loads(Path(sys.argv[1]).read_text())
    print(" ".join(format(v, ".17g") for v in matrix(**request)))
