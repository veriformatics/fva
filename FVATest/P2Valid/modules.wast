;; U28c V5; SpecTec module contexts, imports, globals, data, start + exports.
;; @case imports-closed-refs V5.imports imports use closed recursive reference types
(module (type $a (func (param (ref null $a)))) (import "m" "f" (func (type $a))) (import "m" "g" (global (ref null $a))) (import "m" "t" (table 0 (ref null $a))))
;; @case import-type-oob V5.imports imported function's type index must exist
(assert_invalid (module (import "m" "f" (func (type 2)))) "unknown type")
;; @case import-global-type-oob V5.imports imported global's heap index must exist
(assert_invalid (module (import "m" "g" (global (ref null 3)))) "unknown type")
;; @case global-nonnull V5.global-init ref.func initializer gives a non-null global
(module (func $g) (global (ref func) (ref.func $g)))
;; @case global-typed V5.global-init typed global initializer is closed before matching
(module (type $f (func)) (func $g (type $f)) (global (ref $f) (ref.func $g)))
;; @case global-null-nonnull V5.global-init null cannot initialize a non-null global
(assert_invalid (module (global (ref func) (ref.null func))) "type mismatch")
;; @case global-wrong-family V5.global-init unrelated abstract reference initializer rejected
(assert_invalid (module (global externref (ref.null exn))) "type mismatch")
;; @case global-nonconstant V5.global-init global initializer must be constant
(assert_invalid (module (func $f (result i32) i32.const 0) (global i32 (call $f))) "constant expression required")
;; @case const-imported-immutable V5.const-imported immutable imported global is constant
(module (import "m" "g" (global $g i32)) (global i32 (global.get $g)))
;; @case const-imported-mutable V5.const-imported mutable imported global is not constant
(assert_invalid (module (import "m" "g" (global $g (mut i32))) (global i32 (global.get $g))) "constant expression required")
;; @case const-imported-ref-widen V5.const-imported imported non-null ref can initialize nullable global
(module (import "m" "g" (global $g (ref extern))) (global externref (global.get $g)))
;; @case const-imported-ref-narrow V5.const-imported imported nullable ref cannot initialize non-null global
(assert_invalid (module (import "m" "g" (global $g externref)) (global (ref extern) (global.get $g))) "type mismatch")
;; @case data-offset-import V5.offsets,V5.const-imported data offset may read imported immutable i32 global
(module (import "m" "g" (global $g i32)) (memory 1) (data (global.get $g) "x"))
;; @case elem-offset-import V5.offsets,V5.const-imported element offset may read imported immutable i32 global
(module (import "m" "g" (global $g i32)) (table 1 funcref) (elem (global.get $g) func))
;; @case data-offset-i64 V5.offsets data offset must have the memory address type i32
(assert_invalid (module (memory 1) (data (i64.const 0) "x")) "type mismatch")
;; @case elem-offset-i64 V5.offsets element offset must have the table address type i32
(assert_invalid (module (table 1 funcref) (elem (i64.const 0) func)) "type mismatch")
;; @case data-offset-nonconstant V5.offsets offset must be constant
(assert_invalid (module (func $f (result i32) i32.const 0) (memory 1) (data (call $f) "x")) "constant expression required")
;; @case data-offset-memory-index V5.offsets active data memory index must exist
(assert_invalid (module (data (memory 0) (i32.const 0) "x")) "unknown memory")
;; @case elem-offset-table-index V5.offsets active element table index must exist
(assert_invalid (module (elem (table 0) (i32.const 0) func)) "unknown table")
;; @case start-empty V5.start-exports start function has no params or results
(module (func $f) (start $f))
;; @case start-param V5.start-exports start must not have parameters
(assert_invalid (module (func $f (param i32)) (start $f)) "invalid start function type")
;; @case start-result V5.start-exports start must not have results
(assert_invalid (module (func $f (result i32) i32.const 0) (start $f)) "invalid start function type")
;; @case export-kinds V5.start-exports all five export kinds have distinct names
(module (func $f) (table $t 0 funcref) (memory $m 0) (global $g i32 (i32.const 0)) (tag $e) (export "f" (func $f)) (export "t" (table $t)) (export "m" (memory $m)) (export "g" (global $g)) (export "e" (tag $e)))
;; @case export-duplicate V5.start-exports export names are unique across kinds
(assert_invalid (module (func $f) (tag $t) (export "x" (func $f)) (export "x" (tag $t))) "duplicate export name")
;; @case export-function-index V5.start-exports function export index must exist
(assert_invalid (module (export "f" (func 0))) "unknown function")
;; @case memory-limit-bound V5.limits memory32 limit includes 65536 pages
(module (memory 65536 65536))
;; @case memory-limit-over V5.limits memory32 limit excludes 65537 pages
(assert_invalid (module (memory 65537)) "memory size must be at most")
;; @case table-limit-order V5.limits minimum must not exceed maximum
(assert_invalid (module (table 2 1 funcref)) "size minimum must not be greater than maximum")
;; @case table-limit-empty V5.limits empty table with equal bounds valid
(module (table 0 0 funcref))
;; @case one-memory V5.one-memory one memory permitted
(module (memory 0))
;; @case extended-const-off V5.extended-const arithmetic constant expressions are outside the oracle feature set
(assert_invalid (module (global i32 (i32.add (i32.const 1) (i32.const 2)))) "constant expression required")
