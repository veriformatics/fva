(module
  (import "artifact" "iround" (func $iround (param f64) (result i32)))
  (func (export "counterexample") (result i32)
    i64.const 0x3fdfffffffffffff
    f64.reinterpret_i64
    call $iround))
