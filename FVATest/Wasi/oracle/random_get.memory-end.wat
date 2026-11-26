;; Generated from vectors/random_get.memory-end.json by oracle/make; WASI values remain source-derived.
(module
  (import "wasi_snapshot_preview1" "random_get" (func $random_get (param i32 i32) (result i32)))
  (memory (export "memory") 65536)
  (func $all (param $a i32) (param $n i32) (param $v i32) (result i64)
    (local $i i32)
    (block $bad (loop $next
      (if (i32.ge_u (local.get $i) (local.get $n)) (then (return (i64.const 1))))
      (br_if $bad (i32.ne (i32.load8_u (i32.add (local.get $a) (local.get $i))) (local.get $v)))
      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $next)))
    (i64.const 0))
  (func (export "_start") (result i64)
    (local $o0 i64)
    ;; step 0: random_get; wasmtime
    (local.set $o0 (i64.extend_i32_u (call $random_get (i32.const 4294967295) (i32.const 1))))
    (local.get $o0)
  )
)
