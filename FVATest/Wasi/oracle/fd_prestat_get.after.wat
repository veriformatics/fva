;; Generated from vectors/fd_prestat_get.after.json by oracle/make; WASI values remain source-derived.
(module
  (import "wasi_snapshot_preview1" "fd_prestat_get" (func $fd_prestat_get (param i32 i32) (result i32)))
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
    ;; step 0: fd_prestat_get; wasmtime
    (memory.fill (i32.const 256) (i32.const 170) (i32.const 16))
    (local.set $o0 (i64.extend_i32_u (call $fd_prestat_get (i32.const 3) (i32.const 256))))
    (local.set $o1 (i64.and (i64.and (i64.and (i64.and (i64.and (i64.const 1) (call $all (i32.const 256) (i32.const 1) (i32.const 0))) (call $all (i32.const 257) (i32.const 3) (i32.const 170))) (call $all (i32.const 260) (i32.const 1) (i32.const 1))) (call $all (i32.const 261) (i32.const 3) (i32.const 0))) (call $all (i32.const 264) (i32.const 8) (i32.const 170))))
    (local.get $o0)
    (local.get $o1)
  )
)
