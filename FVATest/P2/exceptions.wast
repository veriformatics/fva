;; U28b S2/S5 + R5: values, clause order, rethrow and store persistence.
(module $exceptions
  (tag $a (param i32 i32))
  (tag $b (param i32 i32))
  (tag $mixed (param i32 i64 f32 f64))
  (global $saved (mut exnref) (ref.null exn))
  (global $mark (mut i32) (i32.const 0))
  (memory 1)
  (func (export "mixed") (param i32 i64 f32 f64) (result i32 i64 f32 f64)
    (block $caught (result i32 i64 f32 f64)
      (try_table (catch $mixed $caught)
        local.get 0
        local.get 1
        local.get 2
        local.get 3
        throw $mixed)
      unreachable))
  (func (export "pair") (param i32 i32) (result i32 i32)
    (block $caught (result i32 i32)
      (try_table (catch $a $caught)
        local.get 0
        local.get 1
        throw $a)
      unreachable))
  (func (export "catch-ref") (param i32 i32) (result i32 i32 i32 i32)
    (local $ref exnref) (local $x i32) (local $y i32)
    (block $outer (result i32 i32)
      (try_table (catch $a $outer)
        (block $inner (result i32 i32 exnref)
          (try_table (catch_ref $a $inner)
            local.get 0
            local.get 1
            throw $a)
          unreachable)
        local.set $ref
        local.set $y
        local.set $x
        local.get $ref
        throw_ref)
      unreachable)
    local.get $x
    local.get $y)
  (func (export "nested") (param i32) (result i32 i32)
    (block $caught (result i32 i32)
      (try_table (catch $a $caught)
        i64.const 777
        (block
          i32.const 123
          (loop
            i64.const 888
            local.get 0
            (if
              (then i32.const 17 i32.const 29 throw $a)
              (else i32.const 31 i32.const 47 throw $a))
            drop)
          drop)
        drop)
      unreachable))
  (func $leaf
    i32.const 53
    i32.const 71
    throw $a)
  (func $middle
    i64.const 333
    call $leaf
    drop)
  (func $deep
    (block
      i32.const 444
      call $middle
      drop))
  (func (export "frames") (result i32 i32)
    (block $caught (result i32 i32)
      (try_table (catch $a $caught)
        call $deep)
      unreachable))
  (func (export "no-match") (result i32 i32)
    (block $outer (result i32 i32)
      (try_table (catch $a $outer)
        (try_table (catch $b $outer)
          (try_table
            i32.const 79
            i32.const 83
            throw $a)))
      unreachable))
  (func (export "all") (result i32)
    (block $caught
      (try_table (catch_all $caught)
        i32.const 5
        i32.const 7
        throw $b)
      i32.const 99
      return)
    i32.const 19)
  (func (export "all-ref") (result i32 i32)
    (block $outer (result i32 i32)
      (try_table (catch $b $outer)
        (block $caught (result exnref)
          (try_table (catch_all_ref $caught)
            i32.const 89
            i32.const 97
            throw $b)
          unreachable)
        throw_ref)
      unreachable))
  (func (export "order-tag-first") (result i32)
    (block $all
      (block $tag (result i32 i32)
        (try_table (catch $b $tag) (catch $a $tag) (catch_all $all)
          i32.const 2
          i32.const 3
          throw $a)
        unreachable)
      i32.sub
      return)
    i32.const 99)
  (func (export "order-all-first") (result i32)
    (block $all
      (block $tag (result i32 i32)
        (try_table (catch_all $all) (catch $a $tag)
          i32.const 2
          i32.const 3
          throw $a)
        unreachable)
      drop
      drop
      i32.const 99
      return)
    i32.const 23)
  (func (export "distinct-tags") (result i32 i32)
    (block $outer (result i32 i32)
      (try_table (catch $a $outer)
        (block $wrong (result i32 i32)
          (try_table (catch $b $wrong)
            i32.const 101
            i32.const 103
            throw $a)
          unreachable)
        drop
        drop
        i32.const -1
        i32.const -2
        return)
      unreachable))
  (func (export "null")
    ref.null exn
    throw_ref)
  (func (export "uncaught")
    i32.const 107
    i32.const 109
    throw $a)
  (func (export "uncaught-deep")
    (block $wrong (result i32 i32)
      (try_table (catch $b $wrong)
        (try_table
          call $deep))
      unreachable)
    drop
    drop)
  (func (export "plain-return") (result i32)
    i32.const 113)
  (func (export "plain-trap")
    unreachable)
  (func (export "save") (param i32 i32)
    (block $caught (result exnref)
      (try_table (catch_all_ref $caught)
        local.get 0
        local.get 1
        throw $a)
      unreachable)
    global.set $saved)
  (func (export "saved") (result i32 i32)
    (block $caught (result i32 i32)
      (try_table (catch $a $caught)
        global.get $saved
        throw_ref)
      unreachable))
  (func (export "store") (result i32 i32 i32)
    (local $x i32) (local $y i32)
    (block $caught (result i32 i32)
      (try_table (catch $a $caught)
        i32.const 127
        global.set $mark
        i32.const 0
        i32.const 131
        i32.store
        i32.const 137
        i32.const 139
        throw $a)
      unreachable)
    local.set $y
    local.set $x
    global.get $mark
    i32.const 0
    i32.load
    local.get $x
    local.get $y
    i32.add))

(assert_return (invoke $exceptions "mixed" (i32.const -17) (i64.const 0x123456789abcdef) (f32.const -0) (f64.const 1.5)) (i32.const -17) (i64.const 0x123456789abcdef) (f32.const -0) (f64.const 1.5)) ;; @covers S2.throw-payload,S2.catch
(assert_return (invoke $exceptions "pair" (i32.const 0) (i32.const -1)) (i32.const 0) (i32.const -1)) ;; @covers S2.catch
(assert_return (invoke $exceptions "pair" (i32.const -2147483648) (i32.const 2147483647)) (i32.const -2147483648) (i32.const 2147483647)) ;; @covers S2.catch
(assert_return (invoke $exceptions "catch-ref" (i32.const 11) (i32.const 29)) (i32.const 11) (i32.const 29) (i32.const 11) (i32.const 29)) ;; @covers S2.catch-ref,S2.rethrow
(assert_return (invoke $exceptions "catch-ref" (i32.const -2147483648) (i32.const 0)) (i32.const -2147483648) (i32.const 0) (i32.const -2147483648) (i32.const 0)) ;; @covers S2.catch-ref,S2.rethrow
(assert_return (invoke $exceptions "nested" (i32.const 1)) (i32.const 17) (i32.const 29)) ;; @covers S2.propagate-label
(assert_return (invoke $exceptions "nested" (i32.const 0)) (i32.const 31) (i32.const 47)) ;; @covers S2.propagate-label
(assert_return (invoke $exceptions "frames") (i32.const 53) (i32.const 71)) ;; @covers S2.propagate-frame
(assert_return (invoke $exceptions "no-match") (i32.const 79) (i32.const 83)) ;; @covers S2.no-match
(assert_return (invoke $exceptions "all") (i32.const 19)) ;; @covers S2.catch-all
(assert_return (invoke $exceptions "all-ref") (i32.const 89) (i32.const 97)) ;; @covers S2.catch-all-ref,S2.rethrow
(assert_return (invoke $exceptions "order-tag-first") (i32.const -1)) ;; @covers S2.clause-order
(assert_return (invoke $exceptions "order-all-first") (i32.const 23)) ;; @covers S2.clause-order
(assert_return (invoke $exceptions "distinct-tags") (i32.const 101) (i32.const 103)) ;; @covers S2.tag-identity
(assert_trap (invoke $exceptions "null") "") ;; @covers S2.throw-ref-null
(assert_exception (invoke $exceptions "uncaught")) ;; @covers S5.uncaught
(assert_exception (invoke $exceptions "uncaught-deep")) ;; @covers S5.uncaught-deep
(assert_return (invoke $exceptions "plain-return") (i32.const 113)) ;; @covers S5.uncaught
(assert_trap (invoke $exceptions "plain-trap") "unreachable") ;; @covers S5.uncaught
(assert_return (invoke $exceptions "store") (i32.const 127) (i32.const 131) (i32.const 276)) ;; @covers S2.rethrow,R5.store-extension
(assert_return (invoke $exceptions "save" (i32.const 149) (i32.const 151))) ;; @covers S2.rethrow,R5.store-extension
(assert_exception (invoke $exceptions "uncaught")) ;; @covers S2.rethrow,R5.store-extension
(assert_return (invoke $exceptions "saved") (i32.const 149) (i32.const 151)) ;; @covers S2.rethrow,R5.store-extension

;; A later module appends a tag and exception; the old exception stays intact.
(module $later
  (tag $t (param i32))
  (func (export "throw") i32.const 157 throw $t))
(assert_exception (invoke $later "throw")) ;; @covers S2.rethrow,R5.store-extension
(assert_return (invoke $exceptions "saved") (i32.const 149) (i32.const 151)) ;; @covers S2.rethrow,R5.store-extension
