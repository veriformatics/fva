;; U28c V4/V5; SpecTec throw, try_table, Catch_ok + Tagtype_ok.
;; @case throw-empty V4.throw zero-parameter tag and polymorphic results
(module (tag $t) (func (result i32 (ref func)) throw $t))
;; @case throw-params V4.throw payload order and stack polymorphism
(module (tag $t (param i32 i64)) (func (result externref) i32.const 1 i64.const 2 throw $t))
;; @case throw-payload-type V4.throw tag parameters must match
(assert_invalid (module (tag $t (param i64)) (func i32.const 1 throw $t)) "type mismatch")
;; @case throw-payload-underflow V4.throw every parameter is required
(assert_invalid (module (tag $t (param i32 i64)) (func i64.const 1 throw $t)) "type mismatch")
;; @case throw-index V4.throw tag index must exist
(assert_invalid (module (tag) (func throw 1)) "unknown tag")
;; @case throw-subtyping V4.throw tag payload operands may widen
(module (tag $t (param funcref)) (func (param (ref func)) local.get 0 throw $t))
;; @case throw-ref-null V4.throw-ref nullable exn operand accepted; results polymorphic
(module (func (result i32 i64) ref.null exn throw_ref))
;; @case throw-ref-nonnull V4.throw-ref non-null exn operand accepted
(module (func (param (ref exn)) (result externref) local.get 0 throw_ref))
;; @case throw-ref-bot V4.throw-ref unknown operand accepted
(module (func (result f64) unreachable throw_ref))
;; @case throw-ref-func V4.throw-ref unrelated reference operand rejected
(assert_invalid (module (func ref.null func throw_ref)) "type mismatch")
;; @case throw-ref-number V4.throw-ref numeric operand rejected
(assert_invalid (module (func i32.const 0 throw_ref)) "type mismatch")
;; @case try-empty V4.try-table no clauses required
(module (func try_table end))
;; @case try-indexed V4.try-table indexed try_table parameters and results
(module (type $b (func (param i32 i64) (result i64 i32))) (func (result i64 i32) i32.const 1 i64.const 2 try_table (type $b) drop drop i64.const 3 i32.const 4 end))
;; @case try-body-result V4.try-table body result must match block result
(assert_invalid (module (func (result i64) try_table (result i64) i32.const 0 end)) "type mismatch")
;; @case try-input-type V4.try-table indexed parameters must match
(assert_invalid (module (type $b (func (param i64))) (func i32.const 0 try_table (type $b) drop end)) "type mismatch")
;; @case catch-tag-payload V4.catch catch payload matches enclosing label
(module (tag $t (param i32)) (func block (result i32) try_table (catch $t 0) end i32.const 0 end drop))
;; @case catch-payload-subtype V4.catch non-null tag payload widens to nullable label
(module (tag $t (param (ref func))) (func block (result funcref) try_table (catch $t 0) end ref.null func end drop))
;; @case catch-payload-nullability V4.catch nullable payload cannot narrow to non-null label
(assert_invalid (module (tag $t (param funcref)) (func block (result (ref func)) try_table (catch $t 0) end unreachable end drop)) "type mismatch")
;; @case catch-payload-count V4.catch payload arity equals target arity
(assert_invalid (module (tag $t (param i32)) (func block try_table (catch $t 0) end end)) "type mismatch")
;; @case catch-label-outside V4.catch clause label zero excludes the try_table's own label
(module (tag $t (param i32)) (func block (result i32) try_table (result i64) (catch $t 0) i64.const 0 end drop i32.const 0 end drop))
;; @case catch-label-index V4.catch,V4.label-depth clause index must exist before entering try_table
(assert_invalid (module (tag $t) (func try_table (catch $t 1) end)) "unknown label")
;; @case catch-tag-index V4.catch clause tag index must exist
(assert_invalid (module (func try_table (catch 0 0) end)) "unknown tag")
;; @case catch-ref-full V4.catch-ref payload precedes a non-null exn reference
(module (tag $t (param i32 i64)) (func block (result i32 i64 (ref exn)) try_table (catch_ref $t 0) end unreachable end drop drop drop))
;; @case catch-ref-widen V4.catch-ref delivered non-null exn may widen to exnref
(module (tag $t) (func block (result exnref) try_table (catch_ref $t 0) end ref.null exn end drop))
;; @case catch-ref-missing-exn V4.catch-ref target must include the exception reference
(assert_invalid (module (tag $t (param i32)) (func block (result i32) try_table (catch_ref $t 0) end i32.const 0 end drop)) "type mismatch")
;; @case catch-ref-wrong-order V4.catch-ref target order must be payload then exception
(assert_invalid (module (tag $t (param i32)) (func block (result exnref i32) try_table (catch_ref $t 0) end ref.null exn i32.const 0 end drop drop)) "type mismatch")
;; @case catch-all-empty V4.catch-all catch_all delivers no payload
(module (func block try_table (catch_all 0) end end))
;; @case catch-all-nonempty V4.catch-all catch_all cannot target a nonempty label
(assert_invalid (module (func block (result i32) try_table (catch_all 0) end i32.const 0 end drop)) "type mismatch")
;; @case catch-all-ref-nonnull V4.catch-all-ref catch_all_ref delivers a non-null exn
(module (func block (result (ref exn)) try_table (catch_all_ref 0) end unreachable end drop))
;; @case catch-all-ref-nullable V4.catch-all-ref delivered exn may widen to nullable
(module (func block (result exnref) try_table (catch_all_ref 0) end ref.null exn end drop))
;; @case catch-all-ref-empty V4.catch-all-ref target must include the exception reference
(assert_invalid (module (func block try_table (catch_all_ref 0) end end)) "type mismatch")
;; @case catch-all-ref-family V4.catch-all-ref delivered exn cannot match externref
(assert_invalid (module (func block (result externref) try_table (catch_all_ref 0) end ref.null extern end drop)) "type mismatch")
;; @case tag-empty V5.tag empty tag function type
(module (type $t (func)) (tag (type $t)))
;; @case tag-typed-params V5.tag tag parameters may include closed typed refs
(module (type $a (func)) (type $t (func (param (ref null $a) exnref))) (tag (type $t)))
;; @case tag-results V5.tag tag function type must have no results
(assert_invalid (module (type $t (func (result i32))) (tag (type $t))) "invalid exception type")
;; @case tag-type-index V5.tag tag type index must exist
(assert_invalid (module (tag (type 3))) "unknown type")
;; @case tag-import-export V5.tag-import-export imports and exports preserve tag type
(module (type $t (func (param i32))) (import "m" "t" (tag $t0 (type $t))) (tag $t1 (param i64)) (export "imported" (tag $t0)) (export "defined" (tag $t1)))
;; @case tag-import-results V5.tag-import-export imported tag type must also have no results
(assert_invalid (module (type $t (func (result i32))) (import "m" "t" (tag (type $t)))) "invalid exception type")
;; @case tag-export-index V5.tag-import-export export tag index must exist
(assert_invalid (module (tag) (export "t" (tag 1))) "unknown tag")
;; @case label-catch-last V4.label-depth catch may target the implicit function label at depth minus one
(module (tag $t) (func try_table (catch $t 0) end))
