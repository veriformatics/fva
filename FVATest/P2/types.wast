;; U28b R1/R3: canonical groups, projections and closure over earlier types.
(module $types
  (rec
    (type $a (func (param i32) (result i32)))
    (type $b (func (param i32) (result i32))))
  (rec
    (type $a2 (func (param i32) (result i32)))
    (type $b2 (func (param i32) (result i32))))
  (type $single (func (param i32) (result i32)))
  (rec (type $r (func (param (ref null $r)) (result i32))))
  (rec (type $r2 (func (param (ref null $r2)) (result i32))))
  (rec
    (type $wide (func (param (ref null $wide)) (result i32)))
    (type $extra (func)))
  (type $base (func (param i64) (result i64)))
  (type $accept (func (param (ref null $base)) (result i32)))
  (type $base2 (func (param i64) (result i64)))
  (type $accept2 (func (param (ref null $base2)) (result i32)))
  (type $pair (func (param i32 i64) (result i32 i64)))
  (table 7 funcref)
  (elem (i32.const 0) $fa $fb $fs $fr $fw $accept-fn $base-fn)
  (func $fa (type $a) (param i32) (result i32)
    local.get 0 i32.const 1 i32.add)
  (func $fb (type $b) (param i32) (result i32)
    local.get 0 i32.const 2 i32.add)
  (func $fs (type $single) (param i32) (result i32)
    local.get 0 i32.const 3 i32.add)
  (func $fr (type $r) (param (ref null $r)) (result i32)
    local.get 0 ref.is_null i32.const 283 i32.add)
  (func $fw (type $wide) (param (ref null $wide)) (result i32)
    local.get 0 ref.is_null i32.const 293 i32.add)
  (func $base-fn (type $base) (param i64) (result i64) local.get 0)
  (func $accept-fn (type $accept) (param (ref null $base)) (result i32)
    local.get 0 ref.is_null i32.const 281 i32.add)
  (func (export "a") (param i32 i32) (result i32)
    local.get 0 local.get 1 call_indirect (type $a2))
  (func (export "b") (param i32 i32) (result i32)
    local.get 0 local.get 1 call_indirect (type $b2))
  (func (export "single") (param i32 i32) (result i32)
    local.get 0 local.get 1 call_indirect (type $single))
  (func (export "recursive") (param i32) (result i32)
    ref.null $r2 local.get 0 call_indirect (type $r2))
  (func (export "earlier-null") (result i32)
    ref.null $base2 i32.const 5 call_indirect (type $accept2))
  (func (export "earlier-func") (result i32)
    ref.func $base-fn i32.const 5 call_indirect (type $accept2))
  (func (export "blocks") (param i32 i64 i32) (result i32 i64)
    local.get 0 local.get 1
    (block (type $pair)
      (loop (type $pair)
        local.get 2
        (if (type $pair)
          (then)
          (else)))))
  (func (export "loop-param") (param i32 i64) (result i32 i64)
    (local $n i32) (local $sum i64)
    local.get 0 local.get 1
    (loop $loop (type $pair)
      local.set $sum local.set $n
      local.get $n
      i32.eqz
      (if (result i32 i64)
        (then local.get $n local.get $sum)
        (else
          local.get $n i32.const 1 i32.sub
          local.get $sum i64.const 7 i64.add
          br $loop)))))

(assert_return (invoke $types "a" (i32.const 307) (i32.const 0)) (i32.const 308)) ;; @covers R1.rec-identity,R3.call-indirect-type
(assert_return (invoke $types "b" (i32.const 307) (i32.const 1)) (i32.const 309)) ;; @covers R1.rec-identity,R3.call-indirect-type
(assert_trap (invoke $types "a" (i32.const 307) (i32.const 1)) "") ;; @covers R1.rec-identity,R3.call-indirect-type
(assert_trap (invoke $types "a" (i32.const 307) (i32.const 2)) "") ;; @covers R1.rec-identity,R3.call-indirect-type
(assert_trap (invoke $types "single" (i32.const 307) (i32.const 0)) "") ;; @covers R1.rec-identity,R3.call-indirect-type
(assert_return (invoke $types "single" (i32.const 307) (i32.const 2)) (i32.const 310)) ;; @covers R1.rec-identity,R3.call-indirect-type
(assert_return (invoke $types "recursive" (i32.const 3)) (i32.const 284)) ;; @covers R1.rec-identity
(assert_trap (invoke $types "recursive" (i32.const 4)) "") ;; @covers R1.rec-identity
(assert_return (invoke $types "earlier-null") (i32.const 282)) ;; @covers R1.nonzero-offset
(assert_return (invoke $types "earlier-func") (i32.const 281)) ;; @covers R1.nonzero-offset
(assert_return (invoke $types "blocks" (i32.const 311) (i64.const 313) (i32.const 0)) (i32.const 311) (i64.const 313)) ;; @covers R3.block-type
(assert_return (invoke $types "blocks" (i32.const -1) (i64.const -2) (i32.const 1)) (i32.const -1) (i64.const -2)) ;; @covers R3.block-type
(assert_return (invoke $types "loop-param" (i32.const 3) (i64.const 317)) (i32.const 0) (i64.const 338)) ;; @covers R3.block-type

(module $exporter
  (rec
    (type $a (func (param i32) (result i32)))
    (type $b (func (param i32) (result i32))))
  (func (export "f") (type $a) (param i32) (result i32)
    local.get 0 i32.const 19 i32.add)
  (rec
    (type $ta (func (param i32)))
    (type $tb (func (param i32))))
  (tag (export "tag") (type $ta)))
(register "typed" $exporter)

(module $same
  (type $earlier (func (param i64)))
  (rec
    (type $a (func (param i32) (result i32)))
    (type $b (func (param i32) (result i32))))
  (rec
    (type $ta (func (param i32)))
    (type $tb (func (param i32))))
  (import "typed" "f" (func $f (type $a)))
  (import "typed" "tag" (tag (type $ta)))
  (func (export "call") (param i32) (result i32)
    local.get 0 call $f)) ;; @covers R1.import-deftype
(assert_return (invoke $same "call" (i32.const 331)) (i32.const 350)) ;; @covers R1.import-deftype

(assert_unlinkable
  (module
    (type $single (func (param i32) (result i32)))
    (import "typed" "f" (func (type $single))))
  "") ;; @covers R1.import-deftype
(assert_unlinkable
  (module
    (rec
      (type $a (func (param i32) (result i32)))
      (type $b (func (param i32) (result i32))))
    (import "typed" "f" (func (type $b))))
  "") ;; @covers R1.import-deftype
(assert_unlinkable
  (module
    (type $single (func (param i32)))
    (import "typed" "tag" (tag (type $single))))
  "") ;; @covers R1.import-deftype
(assert_unlinkable
  (module
    (rec
      (type $ta (func (param i32)))
      (type $tb (func (param i32))))
    (import "typed" "tag" (tag (type $tb))))
  "") ;; @covers R1.import-deftype
