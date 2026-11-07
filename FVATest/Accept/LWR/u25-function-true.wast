;; U25: a mismatched function import must be unlinkable.
(module (func (export "x") (param i32) (result i64) (i64.extend_i32_u (local.get 0))))
(register "provider")
(assert_unlinkable (module (import "provider" "x" (func (param i64) (result i64))))
  "incompatible import type")
