(module
  (import "artifact" "iround" (func $iround (param f64) (result i32)))
  (func (export "observed") (result i32)
    ;; Exact input bits: positive normal, exponent 1021, fraction 2^52 - 1.
    i64.const 0x3fdfffffffffffff
    f64.reinterpret_i64
    call $iround))
