(module
  (import "codec" "memory" (memory 1))
  (import "codec" "lz4BlockEncode" (func $encode (param i32 i32 i32) (result i32)))
  (import "codec" "lz4BlockDecode" (func $decode (param i32 i32 i32) (result i32)))
  (func (export "r1") (result i32) (local $p i32) (local $n i32)
    i32.const 4 memory.grow drop
    (loop $init
      local.get $p i32.const -65536 i32.store
      local.get $p i32.const 4 i32.add local.tee $p
      i32.const 262144 i32.lt_u br_if $init)
    ;; abcdeabcdefgh
    i32.const 262144 i64.const 0x6362616564636261 i64.store
    i32.const 262152 i32.const 0x67666564 i32.store
    i32.const 262156 i32.const 104 i32.store8
    i32.const 262144 i32.const 13 i32.const 262208 call $encode local.set $n
    ;; Return 1 precisely when the size and all 13 output bytes match badBlock.
    local.get $n i32.const 13 i32.eq
    i32.const 262208 i64.load i64.const 0x0005656463626150 i64.eq i32.and
    i32.const 262216 i32.load i32.const 0x67666540 i32.eq i32.and
    i32.const 262220 i32.load8_u i32.const 104 i32.eq i32.and)
  (func (export "r2") (result i32)
    i32.const 100 i64.const 0x6463625000016117 i64.store
    i32.const 108 i32.const 0x6665 i32.store16
    i32.const 100 i32.const 10 i32.const 0 call $decode)
  (func (export "r3_zero") (result i32)
    i32.const 0 i32.const 0 i32.store
    i32.const 0 i32.const 1 i32.const 1024 call $decode)
  (func (export "r3_one") (result i32)
    i32.const 0 i32.const 256 i32.store
    i32.const 0 i32.const 1 i32.const 1024 call $decode)
  (func (export "boundary") (result i32)
    i32.const 65535 i32.const 0 i32.store8
    i32.const 65535 i32.const 1 i32.const 0 call $decode))
