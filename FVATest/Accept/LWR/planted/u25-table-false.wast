;; U25: a matching table import cannot satisfy assert_unlinkable.
(module (table (export "x") 1 3 funcref))
(register "provider")
(assert_unlinkable (module (import "provider" "x" (table 1 3 funcref)))
  "incompatible import type")
