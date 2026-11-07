;; D29/U28a,e + U25: closed rec-group identity includes group shape + projection index.
(module
  (rec (type $a (func)) (type $b (func)))
  (tag (export "tag") (type $a))
  (func (export "fun") (type $a)))
(register "rec-provider")
(module
  (rec (type $a (func)) (type $b (func)))
  (tag $tag (import "rec-provider" "tag") (type $a))
  (func $fun (import "rec-provider" "fun") (type $a))
  (func (export "call-import") (call $fun)))
(assert_return (invoke "call-import"))
(assert_unlinkable
  (module (rec (type $a (func)) (type $b (func)))
    (tag (import "rec-provider" "tag") (type $b)))
  "incompatible import type")
(assert_unlinkable
  (module (type $a (func)) (tag (import "rec-provider" "tag") (type $a)))
  "incompatible import type")
(assert_unlinkable
  (module (rec (type $a (func)) (type $b (func)))
    (func (import "rec-provider" "fun") (type $b)))
  "incompatible import type")
(assert_unlinkable
  (module (type $a (func)) (func (import "rec-provider" "fun") (type $a)))
  "incompatible import type")
