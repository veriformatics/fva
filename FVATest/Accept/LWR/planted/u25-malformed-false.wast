;; U25: valid empty module asserted malformed (planted false assertion).
(assert_malformed (module binary "\00asm\01\00\00\00") "magic header not detected")
