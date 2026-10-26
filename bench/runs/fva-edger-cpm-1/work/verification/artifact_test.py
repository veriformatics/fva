#!/usr/bin/env python3
"""Run the exact shipped module with explicit Wasm imports, using WAST assertions."""
import hashlib
from pathlib import Path
import re
import subprocess
import tempfile

root = Path(__file__).resolve().parent.parent
artifact = (root / 'edgeR.so').read_bytes()
assert hashlib.sha256(artifact).hexdigest() == 'e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb'
wat = subprocess.check_output(['wasm-tools', 'print', str(root / 'edgeR.so')], text=True)
modules = {}
for line in wat.splitlines():
    m = re.fullmatch(r'  \(import "([^"]+)" "([^"]+)" (.*)\)', line)
    if not m:
        continue
    namespace, name, desc = m.groups()
    if desc.startswith('(func'):
        signature = re.sub(r'\(type \d+\)\s*', '', desc)
        signature = re.sub(r'\(;\d+;\)\s*', '', signature)[:-1]
        if name == 'R_chk_calloc':
            body = '(local.get 1) (i32.const 4) (i32.eq) (if (result i32) (then (i32.const 131072)) (else (i32.const 131080)))'
        elif name == 'R_chk_free':
            body = ''
        elif name in ('__cxa_atexit', 'pthread_mutex_init', 'pthread_mutex_destroy'):
            body = 'i32.const 0'
        else:
            body = 'unreachable'
        definition = signature.replace('(func ', f'(func (export "{name}") ', 1) + ' ' + body + ')'
    elif desc.startswith('(global'):
        typ = ' '.join(re.sub(r'\(;\d+;\)\s*', '', desc)[8:-1].split())
        val = 65536 if name == '__stack_pointer' else 0
        definition = f'(global (export "{name}") {typ} (i32.const {val}))'
    elif desc.startswith('(memory'):
        definition = '(memory (export "memory") 4)'
    elif desc.startswith('(table'):
        definition = '(table (export "__indirect_function_table") 9 funcref)'
    else:
        raise AssertionError(desc)
    modules.setdefault(namespace, []).append(definition)

script = []
for i, (namespace, definitions) in enumerate(modules.items()):
    script.append(f'(module $imports{i}\n' + '\n'.join(definitions) + '\n)')
    script.append(f'(register "{namespace}" $imports{i})')
script.append('(module $edgeR binary "' + ''.join(f'\\{b:02x}' for b in artifact) + '")')
script.append('(register "edgeR" $edgeR)')
# The wrapper owns inputs above the module\'s data/static region and separate from scratch.
script.append('''(module $test
  (import "env" "memory" (memory 4))
  (import "edgeR" "__wasm_apply_data_relocs" (func $relocs))
  (import "edgeR" "__wasm_call_ctors" (func $ctors))
  (import "edgeR" "calc_cpm_raw" (func $cpm (param i32 i32 i32 i32)))
  (func (export "initialize") call $relocs call $ctors)
  (func (export "run") (param $c f64) (param $L f64) (result f64)
    ;; y and library-size cmx structs: nrow=ncol=pnrow=1, type=0, isint=0.
    (i32.store (i32.const 32776) (i32.const 1))
    (i32.store (i32.const 32780) (i32.const 1))
    (i32.store (i32.const 32792) (i32.const 1))
    (i32.store (i32.const 32800) (i32.const 32832))
    (i32.store (i32.const 32808) (i32.const 1))
    (i32.store (i32.const 32812) (i32.const 1))
    (i32.store (i32.const 32824) (i32.const 1))
    (f64.store (i32.const 32832) (local.get $L))
    (f64.store (i32.const 32840) (local.get $c))
    (call $cpm (i32.const 32768) (i32.const 32800) (i32.const 32840) (i32.const 1))
    (f64.load (i32.const 32840)))
  (func (export "run2") (result f64 f64)
    (i32.store (i32.const 32776) (i32.const 1))
    (i32.store (i32.const 32780) (i32.const 2))
    (i32.store (i32.const 32792) (i32.const 1))
    (i32.store (i32.const 32800) (i32.const 32832))
    (i32.store (i32.const 32808) (i32.const 1))
    (i32.store (i32.const 32812) (i32.const 2))
    (i32.store (i32.const 32824) (i32.const 1))
    (f64.store (i32.const 32832) (f64.const 18))
    (f64.store (i32.const 32840) (f64.const 18))
    (f64.store (i32.const 32848) (f64.const 10))
    (f64.store (i32.const 32856) (f64.const 10))
    (call $cpm (i32.const 32768) (i32.const 32800) (i32.const 32848) (i32.const 1))
    (f64.load (i32.const 32848)) (f64.load (i32.const 32856)))
  (func (export "formula") (param $c f64) (param $L f64) (result f64)
    local.get $c local.get $L f64.div f64.const 1000000 f64.mul))
(assert_return (invoke $test "initialize"))
(assert_return (invoke $test "run" (f64.const 10) (f64.const 1000000)) (f64.const 10))
(assert_return (invoke $test "run" (f64.const 0x1p+1023) (f64.const 0x1p+1023)) (f64.const inf))
(assert_return (invoke $test "formula" (f64.const 0x1p+1023) (f64.const 0x1p+1023)) (f64.const 1000000))
(assert_return (invoke $test "run" (f64.const 10) (f64.const 18)) (f64.const 0x1.0f4471c71c71cp+19))
(assert_return (invoke $test "formula" (f64.const 10) (f64.const 18)) (f64.const 0x1.0f4471c71c71dp+19))
(assert_return (invoke $test "run2") (f64.const 0x1.0f4471c71c71cp+19) (f64.const 0x1.0f4471c71c71cp+19))
''')
with tempfile.TemporaryDirectory(prefix='edger-wast-') as directory:
    path = Path(directory) / 'artifact.wast'
    path.write_text('\n'.join(script))
    subprocess.run(['wasmtime', 'wast', '-C', 'cache=n', str(path)], check=True)
print('PASS: exact edgeR.so; ordinary CPM = 10; overflow = +inf vs 1000000; boundary differs by one ULP')
