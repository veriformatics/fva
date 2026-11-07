;; U25: a mismatched table import must be unlinkable.
(module (table (export "x") 1 3 funcref))
(register "provider")
(assert_unlinkable (module (import "provider" "x" (table 2 3 funcref)))
  "incompatible import type")
