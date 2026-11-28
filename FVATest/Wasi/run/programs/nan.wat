(func (export "_start")
  (call $effects)
  (drop (f32.add (f32.const nan) (f32.const 1)))
  (call $emit (i32.const 1) (i32.const 16552) (i32.const 6)))
