;; U28b S2: typed reference fields, exnref fields and zero-arity tags.
(module $payload-refs
  (type $op (func (param i32) (result i32)))
  (tag $fields (param i32 (ref $op) i64))
  (tag $inner (param i32))
  (tag $box (param exnref))
  (tag $empty)
  (elem declare func $f $g)
  (func $f (type $op) (param i32) (result i32)
    local.get 0 i32.const 31 i32.add)
  (func $g (type $op) (param i32) (result i32)
    local.get 0 i32.const 37 i32.sub)
  (func (export "fields") (param i32 i64 i32) (result i32 i64)
    (local $k i64)
    (block $caught (result i32 (ref $op) i64 exnref)
      (try_table (catch_ref $fields $caught)
        local.get 0
        local.get 2
        (if (result (ref $op))
          (then ref.func $f)
          (else ref.func $g))
        local.get 1
        throw $fields)
      unreachable)
    drop
    local.set $k
    call_ref $op
    local.get $k)
  (func (export "boxed") (param i32) (result i32)
    (local $saved exnref)
    (block $outer (result i32)
      (try_table (catch $inner $outer)
        (block $boxed (result exnref)
          (try_table (catch $box $boxed)
            (block $saved (result i32 exnref)
              (try_table (catch_ref $inner $saved)
                local.get 0 throw $inner)
              unreachable)
            (local.set 1)
            drop
            (local.get 1)
            throw $box)
          unreachable)
        throw_ref)
      unreachable))
  (func (export "empty") (result i32)
    (block $caught
      (try_table (catch $empty $caught)
        i64.const 839
        throw $empty)
      i32.const -1
      return)
    i32.const 853)
  (func (export "uncaught-empty") throw $empty))

(assert_return (invoke $payload-refs "fields" (i32.const 359) (i64.const -367) (i32.const 1)) (i32.const 390) (i64.const -367)) ;; @covers S2.throw-payload,S2.catch-ref
(assert_return (invoke $payload-refs "fields" (i32.const 359) (i64.const -367) (i32.const 0)) (i32.const 322) (i64.const -367)) ;; @covers S2.throw-payload,S2.catch-ref
(assert_return (invoke $payload-refs "boxed" (i32.const 373)) (i32.const 373)) ;; @covers S2.throw-payload,S2.rethrow
(assert_return (invoke $payload-refs "empty") (i32.const 853)) ;; @covers S2.throw-payload,S2.catch
(assert_exception (invoke $payload-refs "uncaught-empty")) ;; @covers S5.uncaught
