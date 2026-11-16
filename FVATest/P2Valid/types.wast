;; U28c V1/V5; SpecTec 2.1 type validity + 2.2 matching.
;; @case idx-last V1.idx-range heap type at the last available index
(module (type $a (func)) (func (param (ref null $a))))
;; @case idx-param-oob V1.idx-range parameter heap index beyond types
(assert_invalid (module (type (func)) (func (param (ref null 2)))) "unknown type")
;; @case idx-ref-null-oob V1.idx-range ref.null heap index beyond types
(assert_invalid (module (func ref.null 5 drop)) "unknown type")
;; @case idx-call-ref-oob V1.idx-range call_ref type index beyond types
(assert_invalid (module (func unreachable call_ref 7)) "unknown type")
;; @case idx-block-oob V1.idx-range block type index beyond types
(assert_invalid (module (func block (type 6) end)) "unknown type")
;; @case nullable-widen V1.sub-null non-null parameter widens at return
(module (func (param (ref func)) (result funcref) local.get 0))
;; @case nullable-narrow V1.sub-null nullable parameter cannot narrow at return
(assert_invalid (module (func (param funcref) (result (ref func)) local.get 0)) "type mismatch")
;; @case def-func-widen V1.sub-def-func typed ref widens to abstract func
(module (type $a (func)) (func (param (ref $a)) (result (ref func)) local.get 0))
;; @case def-funcref-widen V1.sub-def-func typed nullable ref widens to funcref
(module (type $a (func)) (func (param (ref null $a)) (result funcref) local.get 0))
;; @case abstract-def-narrow V1.sub-def-func abstract func cannot narrow to a defined type
(assert_invalid (module (type $a (func)) (func (param funcref) (result (ref null $a)) local.get 0)) "type mismatch")
;; @case equal-singleton-groups V1.sub-def-identity identical closed singleton groups canonicalize equal
(module (type $a (func)) (type $b (func)) (func (param (ref $a)) (result (ref $b)) local.get 0))
;; @case different-projection V1.sub-def-identity equal signatures at different projections are distinct
(assert_invalid (module (rec (type $a (func)) (type $b (func))) (func (param (ref $a)) (result (ref $b)) local.get 0)) "type mismatch")
;; @case equal-rec-groups V1.sub-def-identity equal recursive groups have equal corresponding projections
(module (rec (type $a (func (param (ref null $b)))) (type $b (func))) (rec (type $c (func (param (ref null $d)))) (type $d (func))) (func (param (ref $a)) (result (ref $c)) local.get 0))
;; @case different-group-shape V1.sub-def-identity a singleton and a two-member group differ despite equal function signatures
(assert_invalid (module (type $a (func)) (rec (type $b (func)) (type $c (func))) (func (param (ref $a)) (result (ref $b)) local.get 0)) "type mismatch")
;; @case different-internal-reference V1.sub-def-identity equal-sized groups with different recursive reference targets differ
(assert_invalid (module (rec (type $a (func (param (ref null $a)))) (type $b (func))) (rec (type $c (func (param (ref null $d)))) (type $d (func))) (func (param (ref $a)) (result (ref $c)) local.get 0)) "type mismatch")
;; @case function-signature-not-subtype V1.sub-def-identity function signature variance does not declare a defined-type subtype
(assert_invalid (module (type $a (func (result (ref func)))) (type $b (func (result funcref))) (func (param (ref $a)) (result (ref $b)) local.get 0)) "type mismatch")
;; @case abstract-self V1.sub-abs abstract references match themselves
(module (func (param exnref externref funcref) (result exnref externref funcref) local.get 0 local.get 1 local.get 2))
;; @case func-not-extern V1.sub-abs func and extern are unrelated
(assert_invalid (module (func (param funcref) (result externref) local.get 0)) "type mismatch")
;; @case extern-not-exn V1.sub-abs extern and exn are unrelated
(assert_invalid (module (func (param externref) (result exnref) local.get 0)) "type mismatch")
;; @case exn-not-func V1.sub-abs exn and func are unrelated
(assert_invalid (module (func (param exnref) (result funcref) local.get 0)) "type mismatch")
;; @case func-not-exn V1.sub-abs func and exn are unrelated
(assert_invalid (module (func (param funcref) (result exnref) local.get 0)) "type mismatch")
;; @case extern-not-func V1.sub-abs extern and func are unrelated
(assert_invalid (module (func (param externref) (result funcref) local.get 0)) "type mismatch")
;; @case exn-not-extern V1.sub-abs exn and extern are unrelated
(assert_invalid (module (func (param exnref) (result externref) local.get 0)) "type mismatch")
;; @case self-rec V1.rec-group,V5.types-seq self reference is inside the current group
(module (type $a (func (param (ref null $a)))))
;; @case mutual-rec V1.rec-group,V5.types-seq forward references within a group are valid
(module (rec (type $a (func (param (ref null $b)))) (type $b (func (result (ref null $a))))))
;; @case rec-forward-outside V1.rec-group forward reference to a later group is invalid
(assert_invalid (module (type $a (func (param (ref null $b)))) (type $b (func))) "unknown type")
;; @case earlier-closed V5.types-seq later groups may refer to earlier groups
(module (type $a (func)) (type $b (func (param (ref null $a)))))
;; @case rec-outside-end V5.types-seq group member refers one beyond the group end
(assert_invalid (module (rec (type (func (param (ref null 2)))) (type (func)))) "unknown type")
;; @case empty-rec V1.rec-group empty recursive group
(module (rec) (type (func)))
;; @case numeric-equality V1.numeric numbers match by equality
(module (func (param i32 i64 f32 f64) (result i32 i64 f32 f64) local.get 0 local.get 1 local.get 2 local.get 3))
;; @case numeric-mismatch V1.numeric numeric widths are not subtypes
(assert_invalid (module (func (param i32) (result i64) local.get 0)) "type mismatch")
;; @case result-pointwise V1.result result subtyping is pointwise
(module (func (param (ref func) (ref extern)) (result funcref externref) local.get 0 local.get 1))
;; @case result-arity V1.result result list lengths must agree
(assert_invalid (module (func (param (ref extern)) (result funcref externref) local.get 0)) "type mismatch")
;; @case ref-null-func V4.ref-null nullable abstract function result
(module (func (result funcref) ref.null func))
;; @case ref-null-exn V4.ref-null nullable exception result
(module (func (result exnref) ref.null exn))
;; @case ref-null-defined V4.ref-null nullable defined type result
(module (type $a (func)) (func (result (ref null $a)) ref.null $a))
;; @case ref-null-not-nonnull V4.ref-null null cannot satisfy a non-null result
(assert_invalid (module (func (result (ref extern)) ref.null extern)) "type mismatch")
;; @case unreachable-ref-null-oob V1.idx-range unreachable does not waive heap-type index validity
(assert_invalid (module (func unreachable ref.null 99 drop)) "unknown type")
;; @case unreachable-block-type-oob V1.idx-range unreachable does not waive block-type index validity
(assert_invalid (module (func unreachable block (type 99) end)) "unknown type")
