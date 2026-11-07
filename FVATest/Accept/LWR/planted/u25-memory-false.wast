;; U25: a matching memory import cannot satisfy assert_unlinkable.
(module (memory (export "x") 1 3))
(register "provider")
(assert_unlinkable (module (import "provider" "x" (memory 1 3)))
  "incompatible import type")
