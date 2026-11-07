;; U25: ordinary module commands must reject mismatched imports too.
(module (func (export "x") (param i32) (result i64) (i64.extend_i32_u (local.get 0))))
(register "provider")
(module (import "provider" "x" (func (param i64) (result i64))))
