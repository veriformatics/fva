;; U28c V1–V5: 2.0 instructions retained under closed-type/subtyping contexts.
;; @case direct-call-widen V4.call-return direct call operands may widen
(module (import "m" "g" (func $g (param funcref))) (func (param (ref func)) local.get 0 call $g))
;; @case direct-call-narrow V4.call-return direct call cannot narrow a nullable argument
(assert_invalid (module (import "m" "g" (func $g (param (ref func)))) (func (param funcref) local.get 0 call $g)) "type mismatch")
;; @case return-widen V4.call-return return result may widen
(module (func (param (ref extern)) (result externref) local.get 0 return))
;; @case return-narrow V4.call-return return cannot narrow a nullable reference
(assert_invalid (module (func (param externref) (result (ref extern)) local.get 0 return)) "type mismatch")
;; @case branch-widen V4.br-if br operand may widen at the target
(module (func (param (ref func)) (result funcref) block (result funcref) local.get 0 br 0 end))
;; @case branch-narrow V4.br-if br cannot narrow a nullable operand
(assert_invalid (module (func (param funcref) (result (ref func)) block (result (ref func)) local.get 0 br 0 end)) "type mismatch")
;; @case branch-if-widen V4.br-if br_if accepts subtype operands and re-pushes label types
(module (func (param (ref func)) (result funcref) block (result funcref) local.get 0 i32.const 0 br_if 0 end))
;; @case branch-if-narrow V4.br-if br_if cannot narrow nullable operands
(assert_invalid (module (func (param funcref) (result (ref func)) block (result (ref func)) local.get 0 i32.const 0 br_if 0 end)) "type mismatch")
;; @case global-get-typed V4.global-ops global.get retains a closed non-null defined type
(module (type $f (func)) (import "m" "g" (global $g (ref $f))) (func (result (ref $f)) global.get $g))
;; @case global-set-widen V4.global-ops global.set accepts a subtype for a mutable reference global
(module (import "m" "g" (global $g (mut funcref))) (func (param (ref func)) local.get 0 global.set $g))
;; @case global-set-narrow V4.global-ops global.set cannot narrow to a mutable non-null global
(assert_invalid (module (import "m" "g" (global $g (mut (ref func)))) (func ref.null func global.set $g)) "type mismatch")
;; @case global-set-immutable V4.global-ops immutable global cannot be set
(assert_invalid (module (import "m" "g" (global $g funcref)) (func ref.null func global.set $g)) "global is immutable")
;; @case memarg-natural-align V4.memarg natural alignment and largest memory32 offset
(module (memory 0) (func i32.const 0 i32.load offset=4294967295 align=4 drop))
;; @case memarg-overalign V4.memarg alignment must not exceed the loaded width
(assert_invalid (module (memory 0) (func i32.const 0 i32.load align=8 drop)) "alignment must not be larger than natural")
;; @case memarg-store-type V4.memarg store value type must match the opcode
(assert_invalid (module (memory 0) (func i32.const 0 i64.const 0 i32.store)) "type mismatch")
;; @case mem-size-grow V4.memory memory32 size and grow return i32
(module (memory 0) (func (result i32) memory.size drop i32.const 0 memory.grow))
;; @case mem-grow-operand V4.memory memory32 grow expects i32
(assert_invalid (module (memory 0) (func i64.const 0 memory.grow drop)) "type mismatch")
;; @case data-drop-index V4.segment-indices data.drop checks segment index
(assert_invalid (module (func data.drop 0)) "unknown data segment")
;; @case elem-drop-index V4.segment-indices elem.drop checks segment index
(assert_invalid (module (func elem.drop 0)) "unknown elem segment")
;; @case segments-passive V4.segment-indices passive data and element indices enter the context
(module (memory 1) (table 1 funcref) (data $d "x") (elem $e funcref (ref.null func)) (func i32.const 0 i32.const 0 i32.const 0 memory.init $d i32.const 0 i32.const 0 i32.const 0 table.init 0 $e data.drop $d elem.drop $e))
;; @case table-limit-u32 V5.limits table32 permits the largest u32 limit without allocation during validation
(module (table 4294967295 4294967295 funcref))
;; @case memory-import-count V5.one-memory one imported memory is valid
(module (import "m" "mem" (memory 0)))
