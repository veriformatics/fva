(module
  (import "codec" "memory" (memory 1))
  (import "codec" "getLinearMemoryOffset" (func $base (result i32)))
  (import "codec" "lz4BlockEncode" (func $encode (param i32 i32 i32) (result i32)))
  (import "codec" "lz4BlockDecode" (func $decode (param i32 i32 i32) (result i32)))
  (data $input "abcdefabcdxyz")
  (data $encoded "\60abcdef\06\00\30xyz")
  (data (i32.const 1024) "\13a\01\00\50aaaaa")
  (func $assert (param i32)
    local.get 0
    if else unreachable end)
  (func (export "r1") (result i32)
    (local $i i32) (local $size i32)
    call $base i32.eqz call $assert
    i32.const 7 memory.grow i32.const 1 i32.eq call $assert
    loop $init
      local.get $i i32.const -65536 i32.store
      local.get $i i32.const 4 i32.add local.tee $i
      i32.const 262144 i32.lt_u br_if $init
    end
    i32.const 262144 i32.const 0 i32.const 13 memory.init $input
    i32.const 500000 i32.const 0 i32.const 13 memory.init $encoded
    i32.const 262144 i32.const 13 i32.const 300000 call $encode
    local.tee $size i32.const 13 i32.eq call $assert
    i32.const 0 local.set $i
    loop $compare
      i32.const 300000 local.get $i i32.add i32.load8_u
      i32.const 500000 local.get $i i32.add i32.load8_u
      i32.eq call $assert
      local.get $i i32.const 1 i32.add local.tee $i
      i32.const 13 i32.lt_u br_if $compare
    end
    local.get $size)
  (func (export "r2") (result i32)
    (local $i i32) (local $size i32)
    i32.const 0 i32.const 204 i32.const 13 memory.fill
    i32.const 1024 i32.const 10 i32.const 0 call $decode
    local.tee $size i32.const 1 i32.eq call $assert
    i32.const 0 i32.load8_u i32.const 97 i32.eq call $assert
    i32.const 1 local.set $i
    loop $unchanged
      local.get $i i32.load8_u i32.const 204 i32.eq call $assert
      local.get $i i32.const 1 i32.add local.tee $i
      i32.const 13 i32.lt_u br_if $unchanged
    end
    local.get $size)
  (func (export "r3") (result i32)
    i32.const 65535 i32.const 0 i32.store8
    i32.const 65535 i32.const 1 i32.const 0 call $decode)
  ;; A harness assertion deliberately made false: the checker must fail here.
  (func (export "falseAssertion") i32.const 0 call $assert)
)
