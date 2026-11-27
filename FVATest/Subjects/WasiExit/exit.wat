;; The minimal WASI command of U29a T6 / U29b T4: `_start` calls `proc_exit 0`.
;; Build: wasm-tools parse exit.wat -o exit.wasm (wasm-tools 1.262.0).
(module
  (type (func (param i32 i32 i32 i32) (result i32)))
  (type (func (param i32)))
  (type (func))
  (import "wasi_snapshot_preview1" "fd_write" (func (type 0)))
  (import "wasi_snapshot_preview1" "proc_exit" (func (type 1)))
  (func (type 2) i32.const 0 call 1)
  (memory 1)
  (export "memory" (memory 0))
  (export "_start" (func 2)))
