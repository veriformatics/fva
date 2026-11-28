(module
  (import "wasi_snapshot_preview1" "fd_write" (func (result i32)))
  (memory (export "memory") 1)
  (func (export "_start")))
