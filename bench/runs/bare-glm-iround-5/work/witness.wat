;; Calls the actual preloaded artifact with an exact binary64 bit pattern.
(module
  (import "shipped" "iround" (func $iround (param f64) (result i32)))
  (func (export "run") (result i32)
    i64.const 0x3fdfffffffffffff
    f64.reinterpret_i64
    call $iround))
