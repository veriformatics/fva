(module
  (import "codec" "memory" (memory 1))
  (import "codec" "lz4BlockDecode" (func $decode (param i32 i32 i32) (result i32)))
  ;; One literal 'a', seven-byte match at offset one, five final 'a' literals.
  (data (i32.const 1024) "\13\61\01\00\50\61\61\61\61\61")
  (data (i32.const 0) "\cc\cc\cc\cc\cc\cc\cc\cc\cc\cc\cc\cc\cc")
  (func (export "run") (result i32)
    (call $decode (i32.const 1024) (i32.const 10) (i32.const 0)))
  (func (export "byte") (param $i i32) (result i32)
    (i32.load8_u (local.get $i))))
(assert_return (invoke "run") (i32.const 1))
(assert_return (invoke "byte" (i32.const 0)) (i32.const 97))
(assert_return (invoke "byte" (i32.const 1)) (i32.const 204))
