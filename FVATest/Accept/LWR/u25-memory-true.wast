;; U25: a mismatched memory import must be unlinkable.
(module (memory (export "x") 1 3))
(register "provider")
(assert_unlinkable (module (import "provider" "x" (memory 2 3)))
  "incompatible import type")
