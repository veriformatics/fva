(module
  (import "wasi_snapshot_preview1" "fd_write" (func $write (param i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 1)
  (data (i32.const 0) "\64\00\00\00\01\00\00\00\65\00\00\00\01\00\00\00")
  (data (i32.const 100) "AB")
  (func (export "two_valid_iovecs") (result i32)
    (drop (call $write (i32.const 1) (i32.const 0) (i32.const 2) (i32.const 64)))
    (i32.load (i32.const 64)))
)
