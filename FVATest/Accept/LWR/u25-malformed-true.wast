;; U25: truncated binary version is a decoder error, not merely validation failure.
(assert_malformed (module binary "\00asm\01\00\00") "unexpected end-of-file")
