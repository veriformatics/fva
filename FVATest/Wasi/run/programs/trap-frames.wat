(func $inner (block (loop (block unreachable))))
(func (export "_start") (call $effects) (block (call $inner)))
