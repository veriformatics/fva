(module
  (import "wasi_snapshot_preview1" "fd_read" (func $read (param i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 18)
  (func (export "probe") (result i32 i32)
    (i32.store (i32.const 0) (i32.const 64))
    (i32.store (i32.const 4) (i32.const 1048576))
    (call $read (i32.const 0) (i32.const 0) (i32.const 1) (i32.const 8))
    (i32.load (i32.const 8))))
