(module
  (import "artifact" "iround" (func $iround (param f64) (result i32)))
  (func (export "run") (result i32)
    i64.const 4602678819172646911
    f64.reinterpret_i64
    call $iround))
