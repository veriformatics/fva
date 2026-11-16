;; U28c R1 = B: a global initializer reads the imported and the earlier defined globals; element
;; initializers and segment offsets read every global.
(module $constants
  (type $v (func (result i32)))
  (func $f (type $v) (i32.const 41))
  (global $a i32 (i32.const 1))
  (global $b i32 (global.get $a))
  (global $c i64 (i64.const 11))
  (global $d i64 (global.get $c))
  (global $fr (ref $v) (ref.func $f))
  (global $gr (ref $v) (global.get $fr))
  (table $t 3 funcref)
  (elem (table $t) (global.get $b) funcref (global.get $gr))
  (memory 1)
  (data (global.get $b) "\2a")
  (func (export "b") (result i32) (global.get $b))
  (func (export "d") (result i64) (global.get $d))
  (func (export "gr") (result i32) (call_ref $v (global.get $gr)))
  (func (export "elem") (result i32) (call_indirect $t (type $v) (i32.const 1)))
  (func (export "data") (result i32) (i32.load8_u (i32.const 1))))

(assert_return (invoke $constants "b") (i32.const 1)) ;; @covers V5.global-prefix
(assert_return (invoke $constants "d") (i64.const 11)) ;; @covers V5.global-prefix
(assert_return (invoke $constants "gr") (i32.const 41)) ;; @covers V5.global-prefix
(assert_return (invoke $constants "elem") (i32.const 41)) ;; @covers V5.segment-globals
(assert_return (invoke $constants "data") (i32.const 42)) ;; @covers V5.segment-globals
