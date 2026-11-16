;; U28c V4/V5; SpecTec table operations, Table_ok, Elem_ok + constant expressions.
;; @case table-get-nonnull V4.table-ops table.get preserves non-null element type
(module (func $g) (table 1 (ref func) (ref.func $g)) (func (result (ref func)) i32.const 0 table.get 0))
;; @case table-set-widen V4.table-ops table.set accepts a subtype of the element type
(module (table 1 funcref) (func (param (ref func)) i32.const 0 local.get 0 table.set 0))
;; @case table-set-narrow V4.table-ops table.set cannot store nullable in a non-null table
(assert_invalid (module (func $g) (table 1 (ref func) (ref.func $g)) (func i32.const 0 ref.null func table.set 0)) "type mismatch")
;; @case table-grow-nonnull V4.table-ops table.grow takes typed value then i32 delta
(module (func $g) (table 1 (ref func) (ref.func $g)) (func (param (ref func)) (result i32) local.get 0 i32.const 1 table.grow 0))
;; @case table-grow-narrow V4.table-ops table.grow rejects nullable initial value for non-null table
(assert_invalid (module (func $g) (table 1 (ref func) (ref.func $g)) (func ref.null func i32.const 1 table.grow 0 drop)) "type mismatch")
;; @case table-fill-widen V4.table-ops table.fill accepts non-null value for nullable table
(module (table 1 externref) (func (param (ref extern)) i32.const 0 local.get 0 i32.const 1 table.fill 0))
;; @case table-fill-family V4.table-ops table.fill rejects an unrelated reference family
(assert_invalid (module (table 1 externref) (func i32.const 0 ref.null func i32.const 1 table.fill 0)) "type mismatch")
;; @case table-size V4.table-ops table.size returns i32
(module (table 0 exnref) (func (result i32) table.size 0))
;; @case table-get-index V4.table-ops table.get checks the table index
(assert_invalid (module (func i32.const 0 table.get 0 drop)) "unknown table")
;; @case table-copy-subtype V4.table-copy-init source element type is below destination
(module (func $g) (table $dst 1 funcref) (table $src 1 (ref func) (ref.func $g)) (func i32.const 0 i32.const 0 i32.const 1 table.copy $dst $src))
;; @case table-copy-reverse V4.table-copy-init nullable source cannot copy into non-null destination
(assert_invalid (module (func $g) (table $dst 1 (ref func) (ref.func $g)) (table $src 1 funcref) (func i32.const 0 i32.const 0 i32.const 1 table.copy $dst $src)) "type mismatch")
;; @case table-init-subtype V4.table-copy-init non-null segment initializes nullable destination
(module (func $g) (table 1 funcref) (elem $e (ref func) (ref.func $g)) (func i32.const 0 i32.const 0 i32.const 1 table.init 0 $e))
;; @case table-init-nullable V4.table-copy-init nullable segment cannot initialize non-null destination
(assert_invalid (module (func $g) (table 1 (ref func) (ref.func $g)) (elem $e funcref (ref.null func)) (func i32.const 0 i32.const 0 i32.const 1 table.init 0 $e)) "type mismatch")
;; @case table-init-identity V4.table-copy-init closed defined-type identity matters for segment-to-table matching
(assert_invalid (module (rec (type $a (func)) (type $b (func))) (table 1 (ref null $a)) (elem $e (ref null $b) (ref.null $b)) (func i32.const 0 i32.const 0 i32.const 1 table.init 0 $e)) "type mismatch")
;; @case table-init-elem-index V4.table-copy-init element segment index must exist
(assert_invalid (module (table 1 funcref) (func i32.const 0 i32.const 0 i32.const 0 table.init 0 0)) "unknown elem segment")
;; @case table-explicit-nonnull V5.table-init explicit constant initializer gives a non-null table
(module (func $g) (table 0 (ref func) (ref.func $g)))
;; @case table-explicit-typed V5.table-init initializer matches a defined element type
(module (type $f (func)) (func $g (type $f)) (table 1 (ref $f) (ref.func $g)))
;; @case table-implicit-null V5.table-init nullable table has a default null initializer
(module (table 0 (ref null exn)))
;; @case table-nonnull-no-init V5.table-init non-null table cannot use the default null initializer
(assert_invalid (module (table 0 (ref func))) "type mismatch")
;; @case table-init-null V5.table-init explicit null cannot initialize non-null table
(assert_invalid (module (table 1 (ref func) (ref.null func))) "type mismatch")
;; @case table-init-nonconstant V5.table-init initializer must be constant
(assert_invalid (module (func $g (result funcref) ref.null func) (table 1 funcref (call $g))) "constant expression required")
;; @case table-init-imported V5.table-init,V5.const-imported imported immutable global is a constant initializer
(module (import "m" "g" (global $g (ref func))) (table 1 (ref func) (global.get $g)))
;; @case elem-declared-nonnull V5.elem-typing declared non-null segment uses non-null initializers
(module (func $g) (elem declare (ref func) (ref.func $g)))
;; @case elem-null-nonnull V5.elem-typing initializer must match the segment's declared nullability
(assert_invalid (module (elem declare (ref func) (ref.null func))) "type mismatch")
;; @case elem-active-widen V5.elem-typing active segment may widen to the table element type
(module (func $g) (table 1 funcref) (elem (table 0) (i32.const 0) (ref func) (ref.func $g)))
;; @case elem-active-narrow V5.elem-typing nullable segment cannot target a non-null table
(assert_invalid (module (func $g) (table 1 (ref func) (ref.func $g)) (elem (table 0) (i32.const 0) funcref (ref.null func))) "type mismatch")
;; @case elem-typed-identity V5.elem-typing declared element type must match the initializer's closed type
(assert_invalid (module (rec (type $a (func)) (type $b (func))) (func $g (type $b)) (elem declare (ref $a) (ref.func $g))) "type mismatch")
;; @case elem-exn-passive V5.elem-typing passive segment may contain exn references
(module (elem exnref (ref.null exn)))
;; @case elem-extern-passive V5.elem-typing passive segment may contain extern references
(module (elem externref (ref.null extern)))
;; @case elem-initializer-nonconstant V5.elem-typing element initializer must be constant
(assert_invalid (module (func $g (result funcref) ref.null func) (elem funcref (call $g))) "constant expression required")
