;; Generated from vectors/path_open.directory-create.json by oracle/make; WASI values remain source-derived.
(module
  (import "wasi_snapshot_preview1" "path_open" (func $path_open (param i32 i32 i32 i32 i32 i64 i64 i32 i32) (result i32)))
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
    ;; step 0: path_open; wasmtime
    (i32.store8 (i32.const 128) (i32.const 110))
    (i32.store8 (i32.const 129) (i32.const 101))
    (i32.store8 (i32.const 130) (i32.const 119))
    (local.set $o0 (i64.extend_i32_u (call $path_open (i32.const 3) (i32.const 0) (i32.const 128) (i32.const 3) (i32.const 3) (i64.const 2) (i64.const 0) (i32.const 0) (i32.const 32))))
    (local.set $o1 (i64.extend_i32_u (i32.load (i32.const 32))))
    (local.get $o0)
    (local.get $o1)
  )
)
