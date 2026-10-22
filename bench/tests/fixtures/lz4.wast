(module
  (import "codec" "memory" (memory 32))
  (import "codec" "COMPRESS" (func $compress (param i32 i32 i32 i32) (result i32)))
  (import "codec" "DECOMPRESS" (func $decompress (param i32 i32 i32 i32) (result i32)))
  (global $length (mut i32) (i32.const 0))
  (data (i32.const 131072) "abaaaaaaaaaba")
  (data (i32.const 327680) "\00")
  (func (export "roundtrip") (result i32) (local $i i32)
    (global.set $length
      (call $compress (i32.const 131072) (i32.const 196608) (i32.const 13) (i32.const 64)))
    (if (i32.le_s (global.get $length) (i32.const 0)) (then (return (i32.const 0))))
    (if (i32.ne
      (call $decompress (i32.const 196608) (i32.const 262144)
        (global.get $length) (i32.const 13)) (i32.const 13))
      (then (return (i32.const 0))))
    (block $done
      (loop $next
        (br_if $done (i32.ge_u (local.get $i) (i32.const 13)))
        (if (i32.ne
          (i32.load8_u (i32.add (i32.const 131072) (local.get $i)))
          (i32.load8_u (i32.add (i32.const 262144) (local.get $i))))
          (then (return (i32.const 0))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $next)))
    (i32.const 1))
  (func (export "empty") (result i32)
    (call $decompress (i32.const 327680) (i32.const 262144) (i32.const 1) (i32.const 0)))
  (func (export "short-output") (result i32)
    (i32.lt_s
      (call $decompress (i32.const 196608) (i32.const 262144)
        (global.get $length) (i32.const 1)) (i32.const 0))))
(assert_return (invoke "roundtrip") (i32.const 1))
(assert_return (invoke "empty") (i32.const 0))
(assert_return (invoke "short-output") (i32.const 1))
