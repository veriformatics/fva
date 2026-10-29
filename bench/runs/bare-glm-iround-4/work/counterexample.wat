(module
  (import "artifact" "iround" (func $iround (param f64) (result i32)))
  (func (export "counterexample") (result i32)
    ;; Exact binary64 input: 1/2 - 2^(-54), immediately below 0.5.
    i64.const 0x3fdfffffffffffff
    f64.reinterpret_i64
    call $iround))
