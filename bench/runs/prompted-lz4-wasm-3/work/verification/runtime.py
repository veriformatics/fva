"""Wasmtime witnesses: import and execute the original, unmodified module."""
from pathlib import Path

def scripts(directory):
    blob = Path('lz4-block-codec.wasm').read_bytes()
    prefix = '(module $codec binary "' + ''.join('\\%02x' % b for b in blob) + '")\n'
    prefix += '(register "codec" $codec)\n'
    r1 = '''(module
      (import "codec" "memory" (memory 1))
      (import "codec" "lz4BlockEncode" (func $enc (param i32 i32 i32) (result i32)))
      (func (export "encode") (result i32) (local $p i32)
        i32.const 4 memory.grow i32.const 1 i32.ne if unreachable end
        (loop $init
          local.get $p i32.const -65536 i32.store
          local.get $p i32.const 4 i32.add local.tee $p
          i32.const 262144 i32.lt_u br_if $init)
        i32.const 262144 i32.const 1684234849 i32.store
        i32.const 262148 i32.const 1684234849 i32.store
        i32.const 262152 i32.const 875770417 i32.store
        i32.const 262156 i32.const 53 i32.store8
        i32.const 262144 i32.const 13 i32.const 262208 call $enc)
      (func (export "byte") (param i32) (result i32) local.get 0 i32.load8_u))
    (assert_return (invoke "encode") (i32.const 13))
    '''
    for i, b in enumerate([64,97,98,99,100,4,0,80,49,50,51,52,53]):
        r1 += f'(assert_return (invoke "byte" (i32.const {262208+i})) (i32.const {b}))\n'
    r2 = '''(module
      (import "codec" "memory" (memory 1))
      (import "codec" "lz4BlockDecode" (func $dec (param i32 i32 i32) (result i32)))
      (data (i32.const 1024) "\\13\\61\\01\\00\\50\\01\\02\\03\\04\\05")
      (func (export "decode") (result i32)
        i32.const 1024 i32.const 10 i32.const 0 call $dec)
      (func (export "byte") (param i32) (result i32) local.get 0 i32.load8_u))
    (assert_return (invoke "decode") (i32.const 1))
    '''
    for i, b in enumerate([97]+[0]*12):
        r2 += f'(assert_return (invoke "byte" (i32.const {i})) (i32.const {b}))\n'
    r3 = '''(module
      (import "codec" "memory" (memory 1))
      (import "codec" "lz4BlockDecode" (func $dec (param i32 i32 i32) (result i32)))
      (data (i32.const 65534) "\\00\\11")
      (func (export "decode") (result i32)
        i32.const 65534 i32.const 1 i32.const 0 call $dec))
    (assert_trap (invoke "decode") "out of bounds memory access")
    '''
    for name, body in [('R1',r1), ('R2',r2), ('R3',r3)]:
        (directory / f'{name}.wast').write_text(prefix + body)
    # A deliberately false runtime assertion must also be rejected.
    (directory / 'wrong-runtime.wast').write_text(prefix + r2.replace(
        '(invoke "decode") (i32.const 1)', '(invoke "decode") (i32.const 13)'))
