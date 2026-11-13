;; U28b S4/R2: both nullable branches and reference value preservation.
(module $references
  (type $ft (func (param i32) (result i32)))
  (elem declare func $f $g)
  (func $f (type $ft) (param i32) (result i32)
    local.get 0 i32.const 7 i32.add)
  (func $g (type $ft) (param i32) (result i32)
    local.get 0 i32.const 13 i32.add)
  (func $pick (param i32) (result (ref null $ft))
    local.get 0
    (if (result (ref null $ft))
      (then ref.func $f)
      (else ref.null $ft)))
  (func (export "call") (param i32 i32) (result i32)
    local.get 1
    local.get 0
    call $pick
    call_ref $ft)
  (func (export "non-null") (param i32 i32) (result i32)
    local.get 1
    local.get 0
    call $pick
    ref.as_non_null
    call_ref $ft)
  (func (export "branch-null") (param i32) (result i32)
    (block $null (result i32)
      i32.const 211
      local.get 0
      call $pick
      br_on_null $null
      call_ref $ft)
    i32.const 1
    i32.add)
  (func (export "branch-non-null") (param i32) (result i32)
    i32.const 211
    (block $non-null (result (ref $ft))
      local.get 0
      call $pick
      br_on_non_null $non-null
      ref.func $g)
    call_ref $ft)
  (func (export "local") (param i32) (result i32)
    (local $r (ref $ft))
    ref.func $g
    local.set $r
    local.get 0
    local.get $r
    call_ref $ft)
  (func (export "local-null") (result i32)
    (local $r (ref $ft))
    ref.func $g local.set $r
    local.get $r ref.is_null)
  (func (export "null-func") (result funcref) ref.null func)
  (func (export "null-extern") (result externref) ref.null extern)
  (func (export "null-exn") (result exnref) ref.null exn)
  (func (export "null-defined") (result (ref null $ft)) ref.null $ft)
  (func (export "null-tests") (result i32 i32 i32 i32 i32)
    ref.null func ref.is_null
    ref.null extern ref.is_null
    ref.null exn ref.is_null
    ref.null $ft ref.is_null
    ref.func $f ref.is_null)
  (func (export "echo-func") (param funcref) (result funcref) local.get 0)
  (func (export "echo-extern") (param externref) (result externref) local.get 0)
  (func $echo-exn (param exnref) (result exnref) local.get 0)
  (func (export "pass-null-exn") (result exnref)
    ref.null exn call $echo-exn))

(assert_return (invoke $references "call" (i32.const 1) (i32.const 223)) (i32.const 230)) ;; @covers S4.call-ref
(assert_trap (invoke $references "call" (i32.const 0) (i32.const 223)) "") ;; @covers S4.call-ref
(assert_return (invoke $references "non-null" (i32.const 1) (i32.const 227)) (i32.const 234)) ;; @covers S4.as-non-null
(assert_trap (invoke $references "non-null" (i32.const 0) (i32.const 227)) "") ;; @covers S4.as-non-null
(assert_return (invoke $references "branch-null" (i32.const 0)) (i32.const 212)) ;; @covers S4.br-on-null
(assert_return (invoke $references "branch-null" (i32.const 1)) (i32.const 219)) ;; @covers S4.br-on-null
(assert_return (invoke $references "branch-non-null" (i32.const 0)) (i32.const 224)) ;; @covers S4.br-on-non-null
(assert_return (invoke $references "branch-non-null" (i32.const 1)) (i32.const 218)) ;; @covers S4.br-on-non-null
(assert_return (invoke $references "local" (i32.const 229)) (i32.const 242)) ;; @covers R2.nondefaultable-local
(assert_return (invoke $references "local-null") (i32.const 0)) ;; @covers R2.nondefaultable-local
(assert_return (invoke $references "null-tests") (i32.const 1) (i32.const 1) (i32.const 1) (i32.const 1) (i32.const 0)) ;; @covers R2.null
(assert_return (invoke $references "null-func") (ref.null)) ;; @covers R2.null
(assert_return (invoke $references "null-func") (ref.null func)) ;; @covers R2.null
(assert_return (invoke $references "null-extern") (ref.null extern)) ;; @covers R2.null
(assert_return (invoke $references "null-exn") (ref.null exn)) ;; @covers R2.null
(assert_return (invoke $references "null-defined") (ref.null)) ;; @covers R2.null
(assert_return (invoke $references "echo-func" (ref.null func)) (ref.null func)) ;; @covers R2.null
(assert_return (invoke $references "echo-extern" (ref.null extern)) (ref.null extern)) ;; @covers R2.null
(assert_return (invoke $references "pass-null-exn") (ref.null)) ;; @covers R2.null
