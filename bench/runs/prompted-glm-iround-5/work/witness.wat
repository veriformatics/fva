(module
  (import "artifact" "iround" (func $iround (param f64) (result i32)))
  (func (export "witness") (result i32)
    f64.const 0x1.fffffffffffffp-2
    call $iround))
