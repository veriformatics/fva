;; U28b R2/R4: non-null initializers and immutable/mutable import variance.
(module $initializers
  (type $ft (func (param i32) (result i32)))
  (func $f (type $ft) (param i32) (result i32)
    local.get 0 i32.const 23 i32.add)
  (func $g (type $ft) (param i32) (result i32)
    local.get 0 i32.const 29 i32.add)
  (elem declare func $f $g)
  (table $filled (export "filled") 3 (ref $ft) (ref.func $f))
  (table $zero 0 (ref $ft) (ref.func $g))
  (table $null 2 funcref (ref.null func))
  (global $gref (export "gref") (ref $ft) (ref.func $g))
  (global $generic (export "generic") (ref func) (ref.func $f))
  (global $nullable (export "nullable") funcref (ref.null func))
  (global $mutable (export "mutable") (mut (ref func)) (ref.func $f))
  (func (export "table-null") (param i32) (result i32)
    local.get 0 table.get $filled ref.is_null)
  (func (export "table-call") (param i32 i32) (result i32)
    local.get 0 local.get 1 call_indirect $filled (type $ft))
  (func (export "sizes") (result i32 i32 i32)
    table.size $filled table.size $zero table.size $null)
  (func (export "null-table") (param i32) (result i32)
    local.get 0 table.get $null ref.is_null)
  (func (export "global-null") (result i32)
    global.get $gref ref.is_null)
  (func (export "global-call") (param i32) (result i32)
    local.get 0 global.get $gref call_ref $ft))
(register "initializers" $initializers)

(assert_return (invoke $initializers "table-null" (i32.const 0)) (i32.const 0)) ;; @covers R2.table-init
(assert_return (invoke $initializers "table-null" (i32.const 2)) (i32.const 0)) ;; @covers R2.table-init
(assert_return (invoke $initializers "table-call" (i32.const 337) (i32.const 0)) (i32.const 360)) ;; @covers R2.table-init
(assert_return (invoke $initializers "table-call" (i32.const 347) (i32.const 2)) (i32.const 370)) ;; @covers R2.table-init
(assert_trap (invoke $initializers "table-call" (i32.const 347) (i32.const 3)) "") ;; @covers R2.table-init
(assert_return (invoke $initializers "sizes") (i32.const 3) (i32.const 0) (i32.const 2)) ;; @covers R2.table-init
(assert_return (invoke $initializers "null-table" (i32.const 0)) (i32.const 1)) ;; @covers R2.table-init,R2.null
(assert_return (invoke $initializers "global-null") (i32.const 0)) ;; @covers R2.global-init
(assert_return (invoke $initializers "global-call" (i32.const 349)) (i32.const 378)) ;; @covers R2.global-init

(module $covariant
  (import "initializers" "generic" (global $g (ref null func)))
  (import "initializers" "mutable" (global $m (mut (ref func))))
  (func (export "globals") (result i32 i32)
    global.get $g ref.is_null
    global.get $m ref.is_null)) ;; @covers R4.global-import-sub
(assert_return (invoke $covariant "globals") (i32.const 0) (i32.const 0)) ;; @covers R4.global-import-sub

(assert_unlinkable
  (module
    (import "initializers" "mutable" (global (mut funcref))))
  "") ;; @covers R4.global-import-sub
(assert_unlinkable
  (module
    (import "initializers" "nullable" (global (ref func))))
  "") ;; @covers R4.global-import-sub
(assert_unlinkable
  (module
    (type $ft (func (param i32) (result i32)))
    (import "initializers" "filled" (table 3 (ref null $ft))))
  "") ;; @covers R2.table-init
