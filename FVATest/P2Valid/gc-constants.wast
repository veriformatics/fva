;; U28c R1 option B: Wasm 3.0 constant expressions, expected = oracle.
;; Global initializers see imports + earlier globals; segments see all globals;
;; table initializers see imported globals only. Every constant global must be immutable.
;; @case defined-global-i32 V5.gc-constants global initializer reads a previous defined immutable i32 global
(module (global $g i32 (i32.const 7)) (global i32 (global.get $g)))
;; @case defined-global-chain V5.gc-constants global initializers see all preceding immutable globals
(module (global $a i64 (i64.const 7)) (global $b i64 (global.get $a)) (global i64 (global.get $b)))
;; @case defined-global-ref V5.gc-constants global initializer reads a previous defined non-null reference global
(module (func $f) (global $g (ref func) (ref.func $f)) (global funcref (global.get $g)))
;; @case defined-data-offset V5.gc-constants data offset reads a defined immutable global
(module (global $g i32 (i32.const 0)) (memory 1) (data (global.get $g) "x"))
;; @case defined-elem-offset V5.gc-constants element offset reads a defined immutable global
(module (global $g i32 (i32.const 0)) (table 1 funcref) (elem (global.get $g) func))
;; @case defined-elem-value V5.gc-constants element initializer reads a defined immutable reference global
(module (global $g funcref (ref.null func)) (elem funcref (global.get $g)))
;; @case defined-table-value V5.gc-constants table initializer cannot see defined globals even under the oracle gc flag
(assert_invalid (module (func $f) (global $g (ref func) (ref.func $f)) (table 1 (ref func) (global.get $g))) "unknown global")
;; @case defined-global-self V5.gc-constants a global initializer cannot read itself
(assert_invalid (module (global $g i32 (global.get $g))) "unknown global")
;; @case defined-global-later V5.gc-constants a global initializer cannot read a later defined global
(assert_invalid (module (global $a i32 (global.get $b)) (global $b i32 (i32.const 0))) "unknown global")
;; @case defined-global-self-after-import V5.gc-constants the first defined global is absent even when imports are present
(assert_invalid (module (import "m" "g" (global i32)) (global $g i32 (global.get $g))) "unknown global")
;; @case defined-global-mutable V5.gc-constants an earlier defined mutable global is not constant
(assert_invalid (module (global $g (mut i32) (i32.const 0)) (global i32 (global.get $g))) "constant expression required")
;; @case defined-data-offset-mutable V5.gc-constants defined mutable global is not a constant data offset
(assert_invalid (module (global $g (mut i32) (i32.const 0)) (memory 1) (data (global.get $g) "x")) "constant expression required")
;; @case defined-elem-offset-mutable V5.gc-constants defined mutable global is not a constant element offset
(assert_invalid (module (global $g (mut i32) (i32.const 0)) (table 1 funcref) (elem (global.get $g) func)) "constant expression required")
;; @case defined-elem-value-mutable V5.gc-constants defined mutable global is not a constant element value
(assert_invalid (module (global $g (mut funcref) (ref.null func)) (elem funcref (global.get $g))) "constant expression required")
;; @case imported-table-value-mutable V5.gc-constants imported mutable global is not a constant table initializer
(assert_invalid (module (import "m" "g" (global $g (mut funcref))) (table 1 funcref (global.get $g))) "constant expression required")
