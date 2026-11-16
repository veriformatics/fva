;; U28c V3/V4; SpecTec Local_ok + Instrs_ok/seq; appendix init stack.
;; @case unset-unused V4.local-get-unset a non-defaultable local need not be read
(module (func (local (ref func))))
;; @case unset-read V4.local-get-unset non-defaultable local starts unset
(assert_invalid (module (func (local (ref func)) local.get 0 drop)) "uninitialized local")
;; @case unset-unreachable V4.local-get-unset unreachable does not initialize locals
(assert_invalid (module (func (local (ref extern)) unreachable local.get 0 drop)) "uninitialized local")
;; @case nullable-default V4.local-get-unset nullable locals are defaultable
(module (func (local funcref externref exnref) local.get 0 drop local.get 1 drop local.get 2 drop))
;; @case set-get V4.local-set-get setting a non-defaultable local permits a later read
(module (func (param (ref func)) (local (ref func)) local.get 0 local.set 1 local.get 1 drop))
;; @case tee-get V4.local-set-get tee both returns the value and initializes
(module (func (param (ref extern)) (local (ref extern)) local.get 0 local.tee 1 drop local.get 1 drop))
;; @case set-null V4.local-set-get set checks the local's non-null type
(assert_invalid (module (func (local (ref func)) ref.null func local.set 0)) "type mismatch")
;; @case tee-null V4.local-set-get tee checks the local's non-null type
(assert_invalid (module (func (local (ref extern)) ref.null extern local.tee 0 drop)) "type mismatch")
;; @case set-one-not-other V4.local-set-get initializing one local leaves its neighbor unset
(assert_invalid (module (func (param (ref func)) (local (ref func) (ref func)) local.get 0 local.set 1 local.get 2 drop)) "uninitialized local")
;; @case repeated-set V4.local-set-get repeated sets do not corrupt the initialization stack
(module (func (param (ref func)) (local (ref func)) local.get 0 local.set 1 block local.get 0 local.set 1 end local.get 1 drop))
;; @case parameter-readable V4.param-set non-defaultable parameter starts set
(module (type $a (func)) (func (param (ref func) (ref extern) (ref exn) (ref $a)) local.get 0 drop local.get 1 drop local.get 2 drop local.get 3 drop))
;; @case parameter-index V4.param-set parameter range still checked
(assert_invalid (module (func (param (ref func)) local.get 1 drop)) "unknown local")
;; @case block-inner-read V4.block-reset initialization is usable inside the same block
(module (func (param (ref func)) (local (ref func)) block local.get 0 local.set 1 local.get 1 drop end))
;; @case block-exit-reset V4.block-reset initialization inside a block ends at its exit
(assert_invalid (module (func (param (ref func)) (local (ref func)) block local.get 0 local.set 1 end local.get 1 drop)) "uninitialized local")
;; @case loop-exit-reset V4.block-reset initialization inside a loop ends at its exit
(assert_invalid (module (func (param (ref func)) (local (ref func)) loop local.get 0 local.set 1 end local.get 1 drop)) "uninitialized local")
;; @case if-exit-reset V4.block-reset both arms setting a local still does not set it after the if
(assert_invalid (module (func (param (ref func)) (local (ref func)) i32.const 0 if local.get 0 local.set 1 else local.get 0 local.set 1 end local.get 1 drop)) "uninitialized local")
;; @case try-exit-reset V4.block-reset initialization inside try_table ends at its exit
(assert_invalid (module (func (param (ref func)) (local (ref func)) try_table local.get 0 local.set 1 end local.get 1 drop)) "uninitialized local")
;; @case entry-set-survives V4.block-reset initialization before constructs survives all their exits
(module (func (param (ref func)) (local (ref func)) local.get 0 local.set 1 block local.get 1 drop end loop local.get 1 drop end i32.const 0 if local.get 1 drop else local.get 1 drop end try_table local.get 1 drop end local.get 1 drop))
;; @case nested-reset-outer-set V4.block-reset exiting an inner block preserves an outer block's set
(module (func (param (ref func)) (local (ref func)) block local.get 0 local.set 1 block local.get 1 drop end local.get 1 drop end))
;; @case nested-inner-reset V4.block-reset an inner block's set does not leak into the outer block
(assert_invalid (module (func (param (ref func)) (local (ref func)) block block local.get 0 local.set 1 end local.get 1 drop end)) "uninitialized local")
;; @case tee-block-reset V4.block-reset tee initialization is also reset at block exit
(assert_invalid (module (func (param (ref func)) (local (ref func)) block local.get 0 local.tee 1 drop end local.get 1 drop)) "uninitialized local")
;; @case if-both-read-own-set V4.if-arms each arm may initialize and read independently
(module (func (param (ref func)) (local (ref func)) i32.const 0 if local.get 0 local.set 1 local.get 1 drop else local.get 0 local.set 1 local.get 1 drop end))
;; @case if-then-not-else V4.if-arms a then-arm initialization is not visible in else
(assert_invalid (module (func (param (ref func)) (local (ref func)) i32.const 0 if local.get 0 local.set 1 else local.get 1 drop end)) "uninitialized local")
;; @case if-else-not-then V4.if-arms an else-arm initialization is not visible in then
(assert_invalid (module (func (param (ref func)) (local (ref func)) i32.const 0 if local.get 1 drop else local.get 0 local.set 1 end)) "uninitialized local")
;; @case if-entry-read V4.if-arms entry initialization is visible in both arms
(module (func (param (ref extern)) (local (ref extern)) local.get 0 local.set 1 i32.const 1 if local.get 1 drop else local.get 1 drop end))
;; @case mixed-runs V3.local-runs mixed defaultable/non-defaultable runs preserve index boundaries
(module (func (param (ref func)) (local i32 i32 (ref func) (ref func) i64) local.get 0 local.set 3 local.get 0 local.set 4 local.get 1 drop local.get 2 drop local.get 3 drop local.get 4 drop local.get 5 drop))
;; @case mixed-runs-unset V3.local-runs adjacent non-defaultable entries have distinct initialization bits
(assert_invalid (module (func (param (ref func)) (local i32 i32 (ref func) (ref func) i64) local.get 0 local.set 3 local.get 4 drop)) "uninitialized local")
;; @case function-init-isolation V3.local-runs initialization state does not leak between functions
(assert_invalid (module (func (param (ref func)) (local (ref func)) local.get 0 local.set 1) (func (local (ref func)) local.get 0 drop)) "uninitialized local")
;; @case repeated-set-direct V4.local-set-get two writes to the same unset local then a read stay valid
(module (func (param (ref func)) (local (ref func)) local.get 0 local.set 1 local.get 0 local.set 1 local.get 1 drop))
