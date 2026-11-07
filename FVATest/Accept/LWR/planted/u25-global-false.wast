;; U25: a matching global import cannot satisfy assert_unlinkable.
(module (global (export "x") i32 (i32.const 9)))
(register "provider")
(assert_unlinkable (module (import "provider" "x" (global i32)))
  "incompatible import type")
