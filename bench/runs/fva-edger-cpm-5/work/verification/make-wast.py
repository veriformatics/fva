"""Generate Wasmtime assertions embedding every byte of the original artifact."""
import hashlib
import pathlib
import re
import subprocess

artifact = pathlib.Path('edgeR.so').read_bytes()
assert hashlib.sha256(artifact).hexdigest() == 'e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb'
wat = subprocess.check_output(['wasm-tools', 'print', 'edgeR.so'], text=True)
namespaces = {'env': [], 'GOT.mem': [], 'GOT.func': []}
for line in wat.splitlines():
    m = re.fullmatch(r'  \(import "([^"]+)" "([^"]+)" (.*)\)', line)
    if not m:
        continue
    ns, name, declaration = m.groups()
    declaration = re.sub(r'\(;.*?;\)', '', declaration)
    declaration = re.sub(r'\(type \d+\)', '', declaration)
    if declaration.startswith('(func'):
        sig = declaration[5:-1]
        if name == 'R_chk_calloc':
            body = '''(local i32)
                global.get $heap local.set 2
                global.get $heap local.get 0 local.get 1 i32.mul i32.add
                i32.const 7 i32.add i32.const -8 i32.and global.set $heap
                local.get 2 i32.const 0 local.get 0 local.get 1 i32.mul memory.fill
                local.get 2'''
        elif name == 'R_chk_free':
            body = ''
        else:
            body = 'unreachable'
        definition = f'(func (export "{name}") {sig} {body})'
    elif declaration.startswith('(global'):
        ty = declaration[7:-1].strip()
        initial = 900000 if name == '__stack_pointer' else 0
        definition = f'(global (export "{name}") {ty} (i32.const {initial}))'
    elif declaration.startswith('(memory'):
        definition = '(memory (export "memory") 16)'
    elif declaration.startswith('(table'):
        definition = '(table (export "__indirect_function_table") 100 funcref)'
    else:
        raise AssertionError(declaration)
    namespaces[ns].append(definition)
out = []
for ns, definitions in namespaces.items():
    extra = '(global $heap (mut i32) (i32.const 65536))' if ns == 'env' else ''
    out.append(f'(module ${ns} {extra}\n' + '\n'.join(definitions) + ')')
    out.append(f'(register "{ns}" ${ns})')
out.append('(module $edge binary "' + ''.join(f'\\{b:02x}' for b in artifact) + '")')
out.append('(register "edge" $edge)')
out.append('''(module $driver
  (import "env" "memory" (memory 16))
  (import "edge" "calc_cpm_raw" (func $raw (param i32 i32 i32 i32)))
  (func (export "cell") (param f64 f64) (result f64)
    (memory.fill (i32.const 32768) (i32.const 0) (i32.const 80))
    (i32.store (i32.const 32768) (i32.const 32832))
    (i32.store (i32.const 32776) (i32.const 1))
    (i32.store (i32.const 32780) (i32.const 1))
    (i32.store (i32.const 32792) (i32.const 1))
    (i32.store (i32.const 32800) (i32.const 32840))
    (i32.store (i32.const 32808) (i32.const 1))
    (i32.store (i32.const 32812) (i32.const 1))
    (i32.store (i32.const 32816) (i32.const 3))
    (i32.store (i32.const 32824) (i32.const 1))
    (f64.store (i32.const 32832) (local.get 0))
    (f64.store (i32.const 32840) (local.get 1))
    (call $raw (i32.const 32768) (i32.const 32800) (i32.const 32832) (i32.const 1))
    (f64.load (i32.const 32832))))
(assert_return (invoke $driver "cell" (f64.const 0x1p+1023) (f64.const 0x1p+1023)) (f64.const inf))
(assert_return (invoke $driver "cell" (f64.const 10) (f64.const 18)) (f64.const 0x1.0f4471c71c71cp+19))
(assert_return (invoke $driver "cell" (f64.const 10) (f64.const 1000000)) (f64.const 10))
''')
pathlib.Path('verification/full-artifact.wast').write_text('\n'.join(out))
print('Generated verification/full-artifact.wast with the exact 96558 artifact bytes')
