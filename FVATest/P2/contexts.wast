;; U28b S1: handlers are outside labels and invisible to branch depths.
(module $contexts
  (tag $t (param i32))
  (type $pair (func (param i32 i64) (result i32 i64)))
  (func (export "body-zero") (result i32)
    (block $caught
      (try_table (result i32) (catch_all $caught)
        i32.const 7
        br 0
        i32.const 91)
      i32.const 10
      i32.add
      return)
    i32.const 99)
  (func (export "outer-branch") (result i32)
    (block $outer (result i32)
      (block $caught
        (try_table (catch_all $caught)
          i32.const 31
          br $outer))
      i32.const 97))
  (func (export "return") (result i32)
    (block $caught
      (try_table (catch_all $caught)
        i32.const 43
        return))
    i32.const 99)
  (func (export "trap-all")
    (block $caught
      (try_table (catch_all $caught)
        (try_table (catch_all $caught)
          unreachable))))
  (func (export "trap-all-ref") (result exnref)
    (block $caught (result exnref)
      (try_table (catch_all_ref $caught)
        unreachable)
      ref.null exn))
  (func (export "normal") (param i32 i64) (result i32 i64)
    (local $a i32) (local $b i64)
    local.get 0
    local.get 1
    (try_table (type $pair)
      local.set $b
      local.set $a
      local.get $a
      i32.const 3
      i32.add
      local.get $b
      i64.const 5
      i64.sub)))

(assert_return (invoke $contexts "body-zero") (i32.const 17)) ;; @covers S1.outside-label
(assert_return (invoke $contexts "outer-branch") (i32.const 31)) ;; @covers S1.br-skips-handler
(assert_return (invoke $contexts "return") (i32.const 43)) ;; @covers S1.return-crosses
(assert_trap (invoke $contexts "trap-all") "unreachable") ;; @covers S1.trap-passes
(assert_trap (invoke $contexts "trap-all-ref") "unreachable") ;; @covers S1.trap-passes
(assert_return (invoke $contexts "normal" (i32.const 11) (i64.const 29)) (i32.const 14) (i64.const 24)) ;; @covers S1.handler-vals
(assert_return (invoke $contexts "normal" (i32.const -3) (i64.const 5)) (i32.const 0) (i64.const 0)) ;; @covers S1.handler-vals
