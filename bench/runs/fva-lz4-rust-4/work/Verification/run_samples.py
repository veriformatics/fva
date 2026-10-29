#!/usr/bin/env python3
"""Run finite regression cases on the unchanged binary; this is not a proof of R1–R3."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
artifact = (ROOT / "lz4-flex.wasm").read_bytes()
assert len(artifact) == 7161
assert hashlib.sha256(artifact).hexdigest() == (
    "1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775"
)
samples = json.loads((ROOT / "Verification/samples.json").read_text())


def quoted(bs):
    return '"' + ''.join(f'\\{b:02x}' for b in bs) + '"'


lines = []
for t in samples:
    src, dst, cap = t['src'], t['dst'], t['cap']
    n = len(t['input'])
    assert cap >= 0 and 131072 <= src <= src + n <= 2097152
    assert 131072 <= dst <= dst + cap <= 2097152
    assert src + n <= dst or dst + cap <= src
    assert len(t['output']) <= cap
    assert t['result'] < 0 or t['result'] <= cap
    lines += [f';; {t["name"]}', '(module $subject binary ' + quoted(artifact) + ')',
              '(register "subject" $subject)', '''(module $harness
  (import "subject" "memory" (memory 32 32))
  (import "subject" "lz4_decompress" (func $decode (param i32 i32 i32 i32) (result i32)))
  (memory 32 32)''',
              f'  (data (i32.const {src}) {quoted(t["input"])})',
              '  (func (export "run") (result i32) (local $r i32)',
              f'    (memory.fill (i32.const {dst}) (i32.const 170) (i32.const {cap}))',
              '    (memory.copy 1 0 (i32.const 131072) (i32.const 131072) (i32.const 1966080))',
              f'    (local.set $r (call $decode (i32.const {src}) (i32.const {dst}) '
              f'(i32.const {len(t["input"])}) (i32.const {cap})))']
    for i, b in enumerate(t['output']):
        lines.append(f'    (if (i32.ne (i32.load8_u (i32.const {dst+i})) (i32.const {b})) '
                     '(then unreachable))')
    lines += ['    (local.get $r))',
              '  (func (export "unchangedOutsideDestination") (result i32) (local $a i32)',
              '    (local.set $a (i32.const 131072))',
              '    (loop $scan',
              f'      (if (i32.or (i32.lt_u (local.get $a) (i32.const {dst})) '
              f'(i32.ge_u (local.get $a) (i32.const {dst+cap})))',
              '        (then (if (i32.ne (i32.load8_u 0 (local.get $a)) '
              '(i32.load8_u 1 (local.get $a))) (then unreachable))))',
              '      (local.set $a (i32.add (local.get $a) (i32.const 1)))',
              '      (br_if $scan (i32.lt_u (local.get $a) (i32.const 2097152))))',
              '    (i32.const 1)))',
              f'(assert_return (invoke $harness "run") (i32.const {t["result"]}))',
              '(assert_return (invoke $harness "unchangedOutsideDestination") (i32.const 1))']

with tempfile.TemporaryDirectory(prefix='lz4-samples-') as tmp:
    wast = Path(tmp) / 'samples.wast'
    wast.write_text('\n'.join(lines) + '\n')
    subprocess.run(['wasmtime', 'wast', '-C', 'cache=n', str(wast)], check=True)
print(f'PASS: {len(samples)} samples; exact results, output prefixes, and final memory '
      'outside destination unchanged. No claim about reads or intermediate writes.')
