(func (export "_start")
  (call $effects)
  ;; Misaligned result pointer = named partial-run boundary, not a guest trap.
  (drop (call $args_sizes (i32.const 65) (i32.const 68))))
