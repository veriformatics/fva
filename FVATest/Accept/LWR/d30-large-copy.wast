;; D30/U26: >=60 KiB copy; every copied byte checked, not only endpoints.
(module
  (memory 2)
  (func (export "copy-60k") (result i32) (local $i i32)
    (memory.fill (i32.const 0) (i32.const 90) (i32.const 61440))
    (memory.fill (i32.const 65536) (i32.const 17) (i32.const 61440))
    (memory.copy (i32.const 65536) (i32.const 0) (i32.const 61440))
    (loop $next
      (if (i32.ne (i32.load8_u (i32.add (i32.const 65536) (local.get $i))) (i32.const 90))
        (then (return (i32.const 1))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br_if $next (i32.lt_u (local.get $i) (i32.const 61440))))
    (i32.or (i32.load8_u (i32.const 61440)) (i32.load8_u (i32.const 126976)))))
(assert_return (invoke "copy-60k") (i32.const 0))
