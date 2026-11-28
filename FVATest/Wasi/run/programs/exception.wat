(tag $e (param i32))
(func (export "_start") (call $effects) (throw $e (i32.const 42)))
