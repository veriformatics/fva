(func (export "_start")
  (call $emit (i32.const 1) (i32.const 16552) (i32.const 6))
  (loop $forever (br $forever)))
