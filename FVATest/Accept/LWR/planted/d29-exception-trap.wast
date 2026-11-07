;; D29/U28e: a trap is not an exception.
(module (func (export "trap") (unreachable)))
(assert_exception (invoke "trap"))
