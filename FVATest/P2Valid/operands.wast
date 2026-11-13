;; U28c V2/V4; SpecTec 2.3 + appendix Bot/pop_ref.
;; @case bot-numbers V2.bot unknown stack operands match every number
(module (func (result i32 i64 f32 f64) unreachable))
;; @case bot-refs V2.bot unknown stack operands match references
(module (func (result (ref func) (ref extern) (ref exn)) unreachable))
;; @case bot-known-number V2.bot known operands after unreachable still need to match
(assert_invalid (module (func (result i64) unreachable i32.const 0)) "type mismatch")
;; @case bot-known-ref V2.bot a known nullable ref does not become non-null on an unreachable stack
(assert_invalid (module (func (result (ref func)) unreachable ref.null func)) "type mismatch")
;; @case refbot-func V2.refbot-as-non-null bottom reference matches non-null func
(module (func (result (ref func)) unreachable ref.as_non_null))
;; @case refbot-extern V2.refbot-as-non-null bottom reference matches non-null extern
(module (func (result (ref extern)) unreachable ref.as_non_null))
;; @case refbot-exn-nullable V2.refbot-as-non-null bottom reference matches nullable exn
(module (func (result exnref) unreachable ref.as_non_null))
;; @case refbot-not-number V2.refbot-as-non-null bottom reference cannot match a numeric result
(assert_invalid (module (func (result i32) unreachable ref.as_non_null)) "type mismatch")
;; @case refbot-br-on-null V2.refbot-br-on-null br_on_null reference bottom matches a non-null extern local
(module (func (local (ref extern)) block unreachable br_on_null 0 local.set 0 end))
;; @case refbot-br-on-null-result V2.refbot-br-on-null br_on_null reference bottom matches a non-null defined local
(module (type $a (func)) (func (local (ref $a)) block unreachable br_on_null 0 local.set 0 end))
;; @case refbot-br-on-null-number V2.refbot-br-on-null reference bottom from br_on_null cannot match i32
(assert_invalid (module (func block unreachable br_on_null 0 i32.eqz drop end)) "type mismatch")
;; @case refbot-br-table V2.refbot-br-table a single bottom reference matches distinct label heap types
(module (type $a (func)) (type $b (func (param i32))) (func block (result (ref $a)) block (result (ref $b)) unreachable ref.as_non_null i32.const 0 br_table 0 1 end drop unreachable end drop))
;; @case refbot-br-table-known V2.refbot-br-table a known reference cannot match unrelated label heap types
(assert_invalid (module (type $a (func)) (type $b (func (param i32))) (func (param (ref $a)) block (result (ref $a)) block (result (ref $b)) local.get 0 i32.const 0 br_table 0 1 end drop unreachable end drop)) "type mismatch")
;; @case as-non-null-func V4.ref-as-non-null narrowing explicit nullability
(module (func (param funcref) (result (ref func)) local.get 0 ref.as_non_null))
;; @case as-non-null-already V4.ref-as-non-null non-null operands remain non-null
(module (func (param (ref extern)) (result (ref extern)) local.get 0 ref.as_non_null))
;; @case as-non-null-number V4.ref-as-non-null a number is not a reference
(assert_invalid (module (func i32.const 0 ref.as_non_null drop)) "type mismatch")
;; @case br-on-null-prefix V4.br-on-null branch keeps the label prefix and narrows the fallthrough reference
(module (func (param funcref) (result i32) block (result i32) i32.const 7 local.get 0 br_on_null 0 drop end))
;; @case br-on-null-bad-prefix V4.br-on-null label prefix must match
(assert_invalid (module (func (param funcref) (result i32) block (result i32) f64.const 0 local.get 0 br_on_null 0 drop end)) "type mismatch")
;; @case br-on-null-bad-label V4.br-on-null,V4.label-depth label index must exist
(assert_invalid (module (func ref.null func br_on_null 1 drop)) "unknown label")
;; @case br-on-non-null V4.br-on-non-null nullable operand branches to a non-null result label
(module (func (param funcref) (result (ref func)) block (result (ref func)) local.get 0 br_on_non_null 0 unreachable end))
;; @case br-on-non-null-nullable-label V4.br-on-non-null target may widen the delivered reference
(module (func (param funcref) (result funcref) block (result funcref) local.get 0 br_on_non_null 0 ref.null func end))
;; @case br-on-non-null-numeric-label V4.br-on-non-null label must end in a reference
(assert_invalid (module (func (param funcref) (result i32) block (result i32) local.get 0 br_on_non_null 0 i32.const 0 end)) "type mismatch")
;; @case br-on-non-null-heap V4.br-on-non-null operand heap type must match the target reference
(assert_invalid (module (func (param externref) (result funcref) block (result funcref) local.get 0 br_on_non_null 0 ref.null func end)) "type mismatch")
;; @case ref-is-null-all V4.ref-is-null every reference family is accepted
(module (type $a (func)) (func (param exnref externref (ref null $a)) local.get 0 ref.is_null drop local.get 1 ref.is_null drop local.get 2 ref.is_null drop))
;; @case ref-is-null-nonnull V4.ref-is-null non-null references accepted
(module (func (param (ref exn)) (result i32) local.get 0 ref.is_null))
;; @case ref-is-null-number V4.ref-is-null numeric operand rejected
(assert_invalid (module (func f32.const 0 ref.is_null drop)) "type mismatch")
;; @case select-ref V4.select typed select accepts reference operands by subtyping
(module (func (param (ref func) funcref) (result funcref) local.get 0 local.get 1 i32.const 0 select (result funcref)))
;; @case select-ref-untyped V4.select untyped select excludes references
(assert_invalid (module (func (param funcref) (result funcref) local.get 0 local.get 0 i32.const 0 select)) "type mismatch")
;; @case select-typed-narrow V4.select typed select cannot narrow nullable operands
(assert_invalid (module (func (param funcref) (result (ref func)) local.get 0 local.get 0 i32.const 0 select (result (ref func)))) "type mismatch")
;; @case select-bot V4.select untyped select accepts pure bottom
(module (func (result f64) unreachable select))
;; @case br-table-subtyping V4.br-table actual non-null operand matches both nullable and non-null labels
(module (func (param (ref func)) block (result funcref) block (result (ref func)) local.get 0 i32.const 0 br_table 0 1 end end drop))
;; @case br-table-nullability V4.br-table nullable actual operand cannot target non-null label
(assert_invalid (module (func (param funcref) block (result (ref func)) block (result funcref) local.get 0 i32.const 0 br_table 0 1 end end drop)) "type mismatch")
;; @case br-table-arity V4.br-table all target label arities must agree
(assert_invalid (module (func block block (result i32) unreachable br_table 0 1 end drop end)) "type mismatch")
;; @case blocktype-multivalue V4.blocktype-idx indexed block consumes params and produces results
(module (type $b (func (param i32 i64) (result i64 i32))) (func (result i64 i32) i32.const 1 i64.const 2 block (type $b) drop drop i64.const 3 i32.const 4 end))
;; @case looptype-params V4.blocktype-idx loop label types are parameters rather than results
(module (type $b (func (param i32) (result i64))) (func (result i64) i32.const 1 loop (type $b) br 0 end))
;; @case iftype-multivalue V4.blocktype-idx both arms receive the indexed block parameters
(module (type $b (func (param i32 i64) (result i32 i64))) (func (result i32 i64) i32.const 1 i64.const 2 i32.const 0 if (type $b) else end))
;; @case blocktype-input V4.blocktype-idx indexed block parameters are checked
(assert_invalid (module (type $b (func (param i64))) (func i32.const 0 block (type $b) drop end)) "type mismatch")
;; @case label-br-last V4.label-depth function's implicit label is the last valid depth
(module (func br 0))
;; @case label-br-depth V4.label-depth br index equal to depth is invalid
(assert_invalid (module (func br 1)) "unknown label")
;; @case label-br-if-last V4.label-depth br_if at depth minus one is valid
(module (func i32.const 0 br_if 0))
;; @case label-br-if-depth V4.label-depth br_if index equal to depth is invalid
(assert_invalid (module (func i32.const 0 br_if 1)) "unknown label")
;; @case label-br-table-last V4.label-depth br_table targets and default at depth minus one are valid
(module (func i32.const 0 br_table 0 0))
;; @case label-br-table-target-depth V4.label-depth br_table explicit target equal to depth is invalid
(assert_invalid (module (func i32.const 0 br_table 1 0)) "unknown label")
;; @case label-br-table-default-depth V4.label-depth br_table default equal to depth is invalid
(assert_invalid (module (func i32.const 0 br_table 0 1)) "unknown label")
;; @case label-br-on-null-last V4.label-depth br_on_null at depth minus one is valid
(module (func ref.null func br_on_null 0 drop))
;; @case refbot-br-table-missing-selector V2.refbot-br-table a bottom reference is not the i32 branch-table selector
(assert_invalid (module (type $a (func)) (type $b (func (param i32))) (func block (result (ref $a)) block (result (ref $b)) unreachable ref.as_non_null br_table 0 1 end drop unreachable end drop)) "type mismatch")
