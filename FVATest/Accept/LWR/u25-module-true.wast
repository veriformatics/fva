;; U25: a matching ordinary import links and calls its registered provider.
(module (func (export "x") (param i32) (result i64) (i64.extend_i32_u (local.get 0))))
(register "provider")
(module
  (import "provider" "x" (func $x (param i32) (result i64)))
  (func (export "probe") (result i64) (call $x (i32.const -1))))
(assert_return (invoke "probe") (i64.const 4294967295))
