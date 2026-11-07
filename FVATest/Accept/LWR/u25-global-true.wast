;; U25: a mismatched global import must be unlinkable.
(module (global (export "x") i32 (i32.const 9)))
(register "provider")
(assert_unlinkable (module (import "provider" "x" (global (mut i32))))
  "incompatible import type")
