(module
  (type (;0;) (func (param f64) (result i32)))
  (memory (;0;) 1)
  (export "memory" (memory 0))
  (export "iround" (func 0))
  (func (;0;) (type 0) (param f64) (result i32)
    local.get 0
    f64.const 0x1p-1 (;=0.5;)
    f64.add
    i32.trunc_sat_f64_s
  )
)
