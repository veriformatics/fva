#!/usr/bin/env python3
"""Compare each certified Lean execution with the unchanged binary in Wasmtime.

The WAST harness checks the return and all 2 MiB of final memory, not merely the
output prefix. This is an independent execution check, not a universal proof.
"""
from pathlib import Path
import json
import subprocess
import tempfile

from extract import ROOT, extract


def quoted(data):
    return '"' + ''.join(f"\\{b:02x}" for b in data) + '"'


def segments(pairs, memory):
    # The Lean finite map uses the first binding for an address.
    values = dict(reversed(pairs))
    values = {a: b for a, b in values.items() if b != 0}
    groups = []
    for address in sorted(values):
        if groups and groups[-1][0] + len(groups[-1][1]) == address:
            groups[-1][1].append(values[address])
        else:
            groups.append((address, [values[address]]))
    return '\n'.join(f"(data (memory {memory}) (i32.const {a}) {quoted(bs)})"
                     for a, bs in groups)


def main():
    assert (ROOT / "Proofs/Artifact.lean").read_text() == extract()
    run = subprocess.run(["lake", "env", "lean", "--run", "verification/Export.lean"],
                         cwd=ROOT, check=True, capture_output=True, text=True)
    cases = json.loads(run.stdout)
    binary = quoted((ROOT / "lz4-c.wasm").read_bytes())
    script = []
    for i, c in enumerate(cases):
        script.append(f'(module $artifact{i} binary {binary})')
        script.append(f'(register "artifact{i}" $artifact{i})')
        initial = segments(c["initial"], 0)
        final = segments(c["final"], 1)
        script.append(f'''(module $harness{i}
  (import "artifact{i}" "memory" (memory 32 32))
  (import "artifact{i}" "LZ4_decompress_safe"
    (func $decode (param i32 i32 i32 i32) (result i32)))
  (memory 32 32)
  {initial}
  {final}
  (func (export "check") (result i32) (local $a i32)
    i32.const {c['src']}
    i32.const {c['dst']}
    i32.const {len(c['input'])}
    i32.const {c['capacity']}
    call $decode
    i32.const {c['return']}
    i32.ne
    if i32.const 0 return end
    loop $compare
      local.get $a
      i32.load8_u 0
      local.get $a
      i32.load8_u 1
      i32.ne
      if i32.const 0 return end
      local.get $a
      i32.const 1
      i32.add
      local.tee $a
      i32.const 2097152
      i32.lt_u
      br_if $compare
    end
    i32.const 1))
(assert_return (invoke $harness{i} "check") (i32.const 1))''')
    with tempfile.TemporaryDirectory(prefix="lz4-verification-") as directory:
        path = Path(directory) / "cases.wast"
        path.write_text('\n'.join(script))
        subprocess.run(["wasmtime", "wast", "-C", "cache=no", str(path)], check=True, cwd=ROOT)
    for c in cases:
        signed = c["return"] if c["return"] < 2**31 else c["return"] - 2**32
        print(f"PASS: {c['name']}: return {signed}, {c['accesses']} accesses; all memory matches")
    print(f"PASS: {len(cases)} exact-artifact Wasmtime checks")


if __name__ == "__main__":
    main()
