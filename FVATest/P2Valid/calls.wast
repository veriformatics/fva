;; U28c V4; SpecTec call_ref, call_indirect, return_call* + C.refs.
;; @case call-ref-nullable V4.call-ref nullable reference accepted
(module (type $f (func (param i32) (result i64))) (func (param (ref null $f)) (result i64) i32.const 0 local.get 0 call_ref $f))
;; @case call-ref-nonnull V4.call-ref non-null reference accepted
(module (type $f (func (param i32) (result i64))) (func (param (ref $f)) (result i64) i32.const 0 local.get 0 call_ref $f))
;; @case call-ref-wrong-defined V4.call-ref equal expansions at different projections are not equal defined types
(assert_invalid (module (rec (type $a (func)) (type $b (func))) (func (param (ref $b)) local.get 0 call_ref $a)) "type mismatch")
;; @case call-ref-abstract V4.call-ref abstract funcref cannot narrow to the callee's type
(assert_invalid (module (type $f (func)) (func (param funcref) local.get 0 call_ref $f)) "type mismatch")
;; @case call-ref-argument V4.call-ref callee parameters are checked below the ref operand
(assert_invalid (module (type $f (func (param i64))) (func (param (ref null $f)) i32.const 0 local.get 0 call_ref $f)) "type mismatch")
;; @case call-ref-equal-groups V1.sub-def-identity,V4.call-ref equal closed groups work at call_ref
(module (type $a (func)) (type $b (func)) (func (param (ref null $b)) local.get 0 call_ref $a))
;; @case return-call-equal V4.return-call direct tail call results equal function results
(module (func $g (param i32) (result i64) i64.const 0) (func (param i32) (result i64) local.get 0 return_call $g))
;; @case return-call-widen V4.return-call callee result non-null is a subtype of caller result nullable
(module (import "m" "g" (func $g (result (ref func)))) (func (result funcref) return_call $g))
;; @case return-call-narrow V4.return-call nullable callee result cannot narrow
(assert_invalid (module (import "m" "g" (func $g (result funcref))) (func (result (ref func)) return_call $g)) "type mismatch")
;; @case return-call-arity V4.return-call tail callee result arity must match
(assert_invalid (module (func $g (result i32) i32.const 0) (func return_call $g)) "type mismatch")
;; @case return-call-params V4.return-call tail call consumes checked parameters
(assert_invalid (module (func $g (param i64)) (func i32.const 0 return_call $g)) "type mismatch")
;; @case return-call-poly V4.return-call tail call discards residual stack and is polymorphic afterward
(module (func $g (result i32) i32.const 1) (func (result i32) f64.const 0 return_call $g f32.const 0 drop))
;; @case return-call-indirect V4.return-call-indirect function table and matching results
(module (type $f (func (param i32) (result i64))) (table 1 funcref) (func (result i64) i32.const 7 i32.const 0 return_call_indirect (type $f)))
;; @case return-call-indirect-widen V4.return-call-indirect callee results may widen
(module (type $f (func (result (ref func)))) (table 1 funcref) (func (result funcref) i32.const 0 return_call_indirect (type $f)))
;; @case return-call-indirect-result V4.return-call-indirect tail results must subtype the caller's results
(assert_invalid (module (type $f (func (result funcref))) (table 1 funcref) (func (result (ref func)) i32.const 0 return_call_indirect (type $f))) "type mismatch")
;; @case return-call-indirect-table V4.return-call-indirect non-function table rejected
(assert_invalid (module (type $f (func)) (table 1 externref) (func i32.const 0 return_call_indirect (type $f))) "type mismatch")
;; @case return-call-indirect-index V4.return-call-indirect table index must exist
(assert_invalid (module (type $f (func)) (func i32.const 0 return_call_indirect 0 (type $f))) "unknown table")
;; @case return-call-ref-nullable V4.return-call-ref nullable callee reference accepted
(module (type $f (func (result i32))) (func (param (ref null $f)) (result i32) local.get 0 return_call_ref $f))
;; @case return-call-ref-widen V4.return-call-ref non-null callee result may widen
(module (type $f (func (result (ref func)))) (func (param (ref $f)) (result funcref) local.get 0 return_call_ref $f))
;; @case return-call-ref-narrow V4.return-call-ref nullable result cannot narrow
(assert_invalid (module (type $f (func (result funcref))) (func (param (ref null $f)) (result (ref func)) local.get 0 return_call_ref $f)) "type mismatch")
;; @case return-call-ref-arity V4.return-call-ref tail result count must match
(assert_invalid (module (type $f (func (result i32))) (func (param (ref null $f)) local.get 0 return_call_ref $f)) "type mismatch")
;; @case return-call-ref-identity V4.return-call-ref reference operand must have the named defined type
(assert_invalid (module (rec (type $a (func)) (type $b (func))) (func (param (ref $b)) local.get 0 return_call_ref $a)) "type mismatch")
;; @case call-indirect-funcref V4.call-indirect nullable function table accepted
(module (type $f (func)) (table 1 funcref) (func i32.const 0 call_indirect (type $f)))
;; @case call-indirect-typed V4.call-indirect typed nullable function table is below funcref
(module (type $f (func)) (table 1 (ref null $f)) (func i32.const 0 call_indirect (type $f)))
;; @case call-indirect-extern V4.call-indirect extern table is not a function table
(assert_invalid (module (type $f (func)) (table 1 externref) (func i32.const 0 call_indirect (type $f))) "type mismatch")
;; @case call-indirect-exn V4.call-indirect exception table is not a function table
(assert_invalid (module (type $f (func)) (table 1 exnref) (func i32.const 0 call_indirect (type $f))) "type mismatch")
;; @case call-indirect-named-mismatch V4.call-indirect table and requested function types may differ; dynamic call can trap
(module (rec (type $a (func)) (type $b (func))) (table 1 (ref null $b)) (func i32.const 0 call_indirect (type $a)))
;; @case ref-func-declared V4.ref-func,V5.refs declarative element declares the function
(module (type $f (func)) (func $g (type $f)) (elem declare func $g) (func (result (ref $f)) ref.func $g))
;; @case ref-func-undeclared V4.ref-func function body alone does not declare the referenced function
(assert_invalid (module (func $g) (func ref.func $g drop)) "undeclared function reference")
;; @case ref-func-index V4.ref-func function index must exist
(assert_invalid (module (func ref.func 2 drop)) "unknown function")
;; @case ref-func-global-declaration V5.refs global initializer contributes to C.refs
(module (func $g) (global funcref (ref.func $g)) (func ref.func $g drop))
;; @case ref-func-table-declaration V5.refs table initializer contributes to C.refs
(module (func $g) (table 1 (ref func) (ref.func $g)) (func ref.func $g drop))
;; @case ref-func-export-declaration V5.refs function export contributes to C.refs
(module (func $g (export "g")) (func ref.func $g drop))
;; @case ref-func-declaration-not-neighbor V5.refs declaring one function does not declare another
(assert_invalid (module (func $g) (func $h) (elem declare func $g) (func ref.func $h drop)) "undeclared function reference")
;; @case call-ref-order-reversed V4.call-ref reference must be above the callee's parameters
(assert_invalid (module (type $f (func (param i32) (result i64))) (func (param (ref null $f)) (result i64) local.get 0 i32.const 0 call_ref $f)) "type mismatch")
;; @case return-call-ref-order V4.return-call-ref args then reference is the required tail-call operand order
(module (type $f (func (param i32) (result i64))) (func (param (ref null $f)) (result i64) i32.const 0 local.get 0 return_call_ref $f))
;; @case return-call-ref-order-reversed V4.return-call-ref reversed tail-call operands are invalid
(assert_invalid (module (type $f (func (param i32) (result i64))) (func (param (ref null $f)) (result i64) local.get 0 i32.const 0 return_call_ref $f)) "type mismatch")
;; @case call-ref-literal-null V4.call-ref literal null typed callee validates although invoking it would trap
(module (type $f (func (param i32) (result i64))) (func (result i64) i32.const 0 ref.null $f call_ref $f))
