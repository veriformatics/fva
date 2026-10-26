"""Generate a WAST harness embedding edgeR.so verbatim; no third-party modules."""
from pathlib import Path
import hashlib
import re
import subprocess

root = Path(__file__).resolve().parent.parent
artifact = (root / 'edgeR.so').read_bytes()
assert len(artifact) == 96558
assert hashlib.sha256(artifact).hexdigest() == 'e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb'
assert hashlib.sha256((root / 'R/filterByExpr.R').read_bytes()).hexdigest() == 'abd43b83d5742dd789fb501ec49d073c690000e23d09604c4d085165a6c92f5f'
wat = subprocess.check_output(['wasm-tools', 'print', str(root / 'edgeR.so')], text=True)
# Derive import signatures from the disassembly, but execute the ORIGINAL binary.
types = dict(re.findall(r'\(type \(;(\d+);\) \(func(.*?)\)\)\n', wat))
imports = re.findall(r'^  \(import "([^"]+)" "([^"]+)" (.*)\)$', wat, re.M)
modules = {}
for namespace, name, descriptor in imports:
    members = modules.setdefault(namespace, [])
    if descriptor.startswith('(func'):
        index = re.search(r'\(type (\d+)\)', descriptor)[1]
        signature = types[index]
        body = 'unreachable'  # fail loudly if any unexpected R service is used
        if name == 'R_chk_calloc':
            # Bump allocator: fresh initially-zero memory, aligned to 8 bytes.
            body = '''(local $old i32)
                global.get $heap local.set $old
                global.get $heap local.get 0 local.get 1 i32.mul i32.add
                i32.const 7 i32.add i32.const -8 i32.and global.set $heap
                local.get $old'''
        elif name == 'R_chk_free':
            body = ''  # freeing these small allocations requires no reuse
        members.append(f'(func (export "{name}") {signature} {body})')
    elif descriptor.startswith('(global'):
        mutable = '(mut i32)' in descriptor
        value = 1000000 if name == '__stack_pointer' else 0
        members.append(f'(global (export "{name}") {"(mut i32)" if mutable else "i32"} (i32.const {value}))')
    elif descriptor.startswith('(memory'):
        members.append(f'(memory (export "{name}") 32)')
    elif descriptor.startswith('(table'):
        members.append(f'(table (export "{name}") 64 funcref)')
    else:
        raise AssertionError(descriptor)

parts = []
for namespace, members in modules.items():
    if namespace == 'env':
        members.append('(global $heap (mut i32) (i32.const 131072))')
        members.append('''(func (export "load") (param i32) (result f64)
            local.get 0 f64.load)''')
        members.append('''(func (export "init") (param $count f64) (param $lib f64)
            ;; cmx at 65536 and 65600: dmat,imat,nrow,ncol,type,isint,pnrow,rowsel.
            i32.const 65536 i32.const 65728 i32.store
            i32.const 65544 i32.const 1 i32.store
            i32.const 65548 i32.const 1 i32.store
            i32.const 65560 i32.const 1 i32.store
            i32.const 65600 i32.const 65736 i32.store
            i32.const 65608 i32.const 1 i32.store
            i32.const 65612 i32.const 1 i32.store
            i32.const 65624 i32.const 1 i32.store
            i32.const 65728 local.get $count f64.store
            i32.const 65736 local.get $lib f64.store
            i32.const 65744 local.get $count f64.store)''')
        members.append('''(func (export "init_boundary")
            ;; Two genes, two libraries. Counts are [10,26] in each column.
            i32.const 65536 i32.const 66000 i32.store
            i32.const 65544 i32.const 2 i32.store
            i32.const 65548 i32.const 2 i32.store
            i32.const 65560 i32.const 2 i32.store
            i32.const 65600 i32.const 66100 i32.store
            i32.const 65608 i32.const 2 i32.store
            i32.const 65612 i32.const 2 i32.store
            i32.const 65616 i32.const 2 i32.store
            i32.const 65624 i32.const 2 i32.store
            i32.const 66000 f64.const 10 f64.store
            i32.const 66008 f64.const 26 f64.store
            i32.const 66016 f64.const 10 f64.store
            i32.const 66024 f64.const 26 f64.store
            i32.const 66100 f64.const 36 f64.store
            i32.const 66108 f64.const 36 f64.store
            i32.const 66200 f64.const 10 f64.store
            i32.const 66208 f64.const 26 f64.store
            i32.const 66216 f64.const 10 f64.store
            i32.const 66224 f64.const 26 f64.store)''')
    parts.append(f'(module ${namespace}\n' + '\n'.join(members) + '\n)')
    parts.append(f'(register "{namespace}" ${namespace})')
parts.append('(module $edge binary "' + ''.join(f'\\{b:02x}' for b in artifact) + '")')
# A normal case also supplies the CPM value used by the R2 witness.
parts.append('''
(invoke $env "init" (f64.const 10) (f64.const 1000000))
(invoke $edge "calc_cpm_raw" (i32.const 65536) (i32.const 65600) (i32.const 65744) (i32.const 1))
(assert_return (invoke $env "load" (i32.const 65744)) (f64.const 10))
;; Finite, exactly representable c=L=2^1020; mathematical CPM is 1000000.
(invoke $env "init" (f64.const 0x1p+1020) (f64.const 0x1p+1020))
(invoke $edge "calc_cpm_raw" (i32.const 65536) (i32.const 65600) (i32.const 65744) (i32.const 1))
(assert_return (invoke $env "load" (i32.const 65744)) (f64.const inf))
;; The requirement's division-first expression is exact for the SAME inputs.
(module $reference
  (func (export "cpm") (result f64)
    f64.const 0x1p+1020 f64.const 0x1p+1020 f64.div
    f64.const 1000000 f64.mul))
(assert_return (invoke $reference "cpm") (f64.const 1000000))
''')
# One fixed CPM table is shared with the R adapter and checked cell by cell.
expected = [float.fromhex('0x1.0f4471c71c71cp+18'), 26.0 * 1000000.0 / 36.0] * 2
parts.append('(invoke $env "init_boundary")')
parts.append('(invoke $edge "calc_cpm_raw" (i32.const 65536) (i32.const 65600) (i32.const 66200) (i32.const 1))')
for i, value in enumerate(expected):
    parts.append(f'(assert_return (invoke $env "load" (i32.const {66200 + i * 8})) (f64.const {value.hex()}))')
(root / 'verification/artifact_cpm.R').write_text('matrix(c(' + ','.join(value.hex() for value in expected) + '), nrow=2)\n')
(root / 'verification/witness.wast').write_text('\n'.join(parts))
subprocess.run(['wasmtime', 'wast', '-C', 'cache=n', str(root / 'verification/witness.wast')], check=True)
print('PASS: exact artifact returns CPM=10 for (10,1000000), +inf for (2^1020,2^1020); reference=1000000')
print('PASS: all four CPM cells of R2 boundary input agree bit-for-bit with verification/artifact_cpm.R')
