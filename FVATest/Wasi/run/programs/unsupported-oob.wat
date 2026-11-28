(func (export "_start")
  (call $effects)
  (i32.store (i32.const 0) (i32.const 16544))
  (i32.store (i32.const 4) (i32.const 2))
  ;; Wasmtime can emit before this bad result-pointer traps. FVA must stop first.
  (drop (call $write (i32.const 1) (i32.const 0) (i32.const 1) (i32.const 65536))))
