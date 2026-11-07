(module (func (export "answer") (result i32) i32.const 7))
(assert_return (invoke "answer") (i32.const 7)) (assert_return (invoke "answer") (i32.const 8))
(assert_trap (invoke "answer") "unreachable")
