;; U25: valid binary grammar, invalid result typing. assert_malformed is false.
;; Grammar: one ()->i32 type, one function of that type, body with no locals + end.
;; Independent controls: wasm-tools print succeeds; wasm-tools validate rejects.
;; Wasmtime's WAST harness conflates malformed/invalid and accepts this false assertion.
(assert_malformed
  (module binary "\00asm\01\00\00\00\01\05\01\60\00\01\7f\03\02\01\00\0a\04\01\02\00\0b")
  "type mismatch")
