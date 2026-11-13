;; U28b S3: all three tail-call forms, callee/host results and handler lifetime.
(module $tail
  (type $sig (func (param i32 i64) (result i64 i32)))
  (type $zero (func (result i32)))
  (type $print (func (param i32)))
  (import "spectest" "print_i32" (func $print (type $print)))
  (tag $t (param i32))
  (table 5 funcref)
  (elem (i32.const 0) $mix $wrong $throw $print)
  (elem declare func $recur)
  (func $mix (type $sig) (param $a i32) (param $b i64) (result i64 i32)
    local.get $b
    i64.const 7
    i64.sub
    local.get $a
    i32.const 5
    i32.add)
  (func $wrong (result i32) i32.const 199)
  (func $throw (result i32) i32.const 181 throw $t)
  (func $recur (export "recur") (param $n i32) (param $sum i32) (result i32)
    local.get $n
    i32.eqz
    (if (result i32)
      (then local.get $sum)
      (else
        local.get $n i32.const 1 i32.sub
        local.get $sum i32.const 3 i32.add
        return_call $recur)))
  (func (export "direct") (param i32 i64) (result i64 i32)
    i32.const 901
    (block
      i64.const 902
      (block
        local.get 0
        local.get 1
        return_call $mix)
      drop)
    drop
    unreachable)
  (func (export "ref") (param i32 i64) (result i64 i32)
    local.get 0
    local.get 1
    ref.func $mix
    return_call_ref $sig)
  (func (export "null-ref") (param i32 i64) (result i64 i32)
    local.get 0
    local.get 1
    ref.null $sig
    return_call_ref $sig)
  (func (export "indirect") (param i32 i64 i32) (result i64 i32)
    local.get 0
    local.get 1
    local.get 2
    return_call_indirect (type $sig))
  (func $drop-direct (export "drop-direct") (result i32)
    (block $caught (result i32)
      (try_table (result i32) (catch $t $caught)
        return_call $throw)))
  (func (export "drop-ref") (result i32)
    (block $caught (result i32)
      (try_table (result i32) (catch $t $caught)
        ref.func $throw
        return_call_ref $zero)))
  (func (export "drop-indirect") (result i32)
    (block $caught (result i32)
      (try_table (result i32) (catch $t $caught)
        i32.const 2
        return_call_indirect (type $zero))))
  (func (export "keep-ordinary") (result i32)
    (block $caught (result i32)
      (try_table (result i32) (catch $t $caught)
        call $throw)))
  (func (export "outer-caller") (result i32)
    (block $caught (result i32)
      (try_table (result i32) (catch $t $caught)
        call $drop-direct)))
  (func (export "host-direct") (param i32)
    (block
      local.get 0
      return_call $print))
  (func (export "host-ref") (param i32)
    local.get 0
    ref.func $print
    return_call_ref $print)
  (func (export "host-indirect") (param i32)
    local.get 0
    i32.const 3
    return_call_indirect (type $print)))

(assert_return (invoke $tail "direct" (i32.const 11) (i64.const 37)) (i64.const 30) (i32.const 16)) ;; @covers S3.return-call,S3.drops-labels
(assert_return (invoke $tail "direct" (i32.const -5) (i64.const 7)) (i64.const 0) (i32.const 0)) ;; @covers S3.return-call,S3.drops-labels
(assert_return (invoke $tail "recur" (i32.const 0) (i32.const 17)) (i32.const 17)) ;; @covers S3.return-call
(assert_return (invoke $tail "recur" (i32.const 12000) (i32.const 17)) (i32.const 36017)) ;; @covers S3.return-call
(assert_return (invoke $tail "ref" (i32.const 13) (i64.const 41)) (i64.const 34) (i32.const 18)) ;; @covers S3.return-call-ref
(assert_trap (invoke $tail "null-ref" (i32.const 13) (i64.const 41)) "") ;; @covers S3.return-call-ref
(assert_return (invoke $tail "indirect" (i32.const 17) (i64.const 43) (i32.const 0)) (i64.const 36) (i32.const 22)) ;; @covers S3.return-call-indirect
(assert_trap (invoke $tail "indirect" (i32.const 17) (i64.const 43) (i32.const 1)) "") ;; @covers S3.return-call-indirect
(assert_trap (invoke $tail "indirect" (i32.const 17) (i64.const 43) (i32.const 4)) "") ;; @covers S3.return-call-indirect
(assert_trap (invoke $tail "indirect" (i32.const 17) (i64.const 43) (i32.const 5)) "") ;; @covers S3.return-call-indirect
(assert_trap (invoke $tail "indirect" (i32.const 17) (i64.const 43) (i32.const -1)) "") ;; @covers S3.return-call-indirect
(assert_exception (invoke $tail "drop-direct")) ;; @covers S1.tail-drops-handler
(assert_exception (invoke $tail "drop-ref")) ;; @covers S1.tail-drops-handler
(assert_exception (invoke $tail "drop-indirect")) ;; @covers S1.tail-drops-handler
(assert_return (invoke $tail "keep-ordinary") (i32.const 181)) ;; @covers S1.tail-drops-handler
(assert_return (invoke $tail "outer-caller") (i32.const 181)) ;; @covers S1.tail-drops-handler
(assert_return (invoke $tail "host-direct" (i32.const 191))) ;; @covers S3.return-call
(assert_return (invoke $tail "host-ref" (i32.const 193))) ;; @covers S3.return-call-ref
(assert_return (invoke $tail "host-indirect" (i32.const 197))) ;; @covers S3.return-call-indirect
