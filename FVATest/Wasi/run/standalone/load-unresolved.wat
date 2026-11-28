(module
  (import "not_wasi" "never_called" (func))
  (memory (export "memory") 1)
  (func (export "_start")))
