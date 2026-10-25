;; Same valid block [00], same pointers. Only the byte AFTER the block changes.
(module
  (import "codec" "memory" (memory 1))
  (import "codec" "lz4BlockDecode" (func $decode (param i32 i32 i32) (result i32)))
  (data (i32.const 4095) "\2a")
  (func (export "zero_suffix") (result i32)
    (call $decode (i32.const 1024) (i32.const 1) (i32.const 4096)))
  (func (export "one_suffix") (result i32)
    (i32.store8 (i32.const 1025) (i32.const 1))
    (call $decode (i32.const 1024) (i32.const 1) (i32.const 4096)))
  (func (export "byte") (param $i i32) (result i32)
    (i32.load8_u (i32.add (i32.const 4096) (local.get $i)))))
(assert_return (invoke "zero_suffix") (i32.const 0))
(assert_return (invoke "one_suffix") (i32.const 4))
(assert_return (invoke "byte" (i32.const 0)) (i32.const 42))
(assert_return (invoke "byte" (i32.const 1)) (i32.const 42))
(assert_return (invoke "byte" (i32.const 2)) (i32.const 42))
(assert_return (invoke "byte" (i32.const 3)) (i32.const 42))
;; The valid block [00] also occupies the final byte of the same one-page
;; memory, untouched by the preceding calls. Output is safely in bounds.
(assert_trap
  (invoke $codec "lz4BlockDecode" (i32.const 65535) (i32.const 1) (i32.const 1024))
  "out of bounds memory access")
