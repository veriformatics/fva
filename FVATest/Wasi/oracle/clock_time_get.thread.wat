;; Generated from vectors/clock_time_get.thread.json by oracle/make; WASI values remain source-derived.
(module
  (import "wasi_snapshot_preview1" "clock_time_get" (func $clock_time_get (param i32 i64 i32) (result i32)))
  (memory (export "memory") 1)
  (func $all (param $a i32) (param $n i32) (param $v i32) (result i64)
    (local $i i32)
    (block $bad (loop $next
      (if (i32.ge_u (local.get $i) (local.get $n)) (then (return (i64.const 1))))
      (br_if $bad (i32.ne (i32.load8_u (i32.add (local.get $a) (local.get $i))) (local.get $v)))
      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $next)))
    (i64.const 0))
  (func (export "_start") (result i64 i64)
    (local $o0 i64)
    (local $o1 i64)
    ;; step 0: clock_time_get; wasmtime
    (local.set $o0 (i64.extend_i32_u (call $clock_time_get (i32.const 3) (i64.const 0) (i32.const 40))))
    (local.set $o1 (i64.load (i32.const 40)))
    (local.get $o0)
    (local.get $o1)
  )
)
