;; D29/U28e: assert_exception succeeds only for an escaping exception.
(module (func (export "normal")) (func (export "trap") (unreachable)))
(assert_exception (invoke "normal"))
