;; Generated runtime harness: imports and executes the original artifact.
(module
  (import "decoder" "memory" (memory 32 32))
  (import "decoder" "lz4_decompress" (func $decode (param i32 i32 i32 i32) (result i32)))
  (func $expect (param i32) local.get 0 i32.eqz if unreachable end)
  (func $check_fill (param $p i32) (param $end i32) (param $value i32)
    block loop local.get $p local.get $end i32.ge_u br_if 1
      local.get $p i32.load8_u local.get $value i32.eq call $expect
      local.get $p i32.const 1 i32.add local.set $p br 0 end end)
  (func (export "check") (result i32)
    ;; empty_input
    i32.const 131072 i32.const 90 i32.const 1966080 memory.fill
    i32.const 262144 i32.const 165 i32.const 0 memory.fill
    i32.const 131072 i32.const 262144 i32.const 0 i32.const 0
    call $decode i32.const -1 i32.eq call $expect
    i32.const 131072 i32.const 262144 i32.const 90 call $check_fill
    i32.const 262144 i32.const 2097152 i32.const 90 call $check_fill
    ;; empty_block
    i32.const 131072 i32.const 90 i32.const 1966080 memory.fill
    i32.const 262144 i32.const 165 i32.const 0 memory.fill
    i32.const 131072 i32.const 0 i32.store8
    i32.const 131072 i32.const 262144 i32.const 1 i32.const 0
    call $decode i32.const 0 i32.eq call $expect
    i32.const 131072 i32.load8_u i32.const 0 i32.eq call $expect
    i32.const 131073 i32.const 262144 i32.const 90 call $check_fill
    i32.const 262144 i32.const 2097152 i32.const 90 call $check_fill
    ;; one_literal
    i32.const 131072 i32.const 90 i32.const 1966080 memory.fill
    i32.const 262144 i32.const 165 i32.const 1 memory.fill
    i32.const 131072 i32.const 16 i32.store8
    i32.const 131073 i32.const 65 i32.store8
    i32.const 131072 i32.const 262144 i32.const 2 i32.const 1
    call $decode i32.const 1 i32.eq call $expect
    i32.const 262144 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 131072 i32.load8_u i32.const 16 i32.eq call $expect
    i32.const 131073 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 131074 i32.const 262144 i32.const 90 call $check_fill
    i32.const 262145 i32.const 2097152 i32.const 90 call $check_fill
    ;; slow_overlap
    i32.const 131072 i32.const 90 i32.const 1966080 memory.fill
    i32.const 262144 i32.const 165 i32.const 13 memory.fill
    i32.const 131072 i32.const 19 i32.store8
    i32.const 131073 i32.const 65 i32.store8
    i32.const 131074 i32.const 1 i32.store8
    i32.const 131075 i32.const 0 i32.store8
    i32.const 131076 i32.const 80 i32.store8
    i32.const 131077 i32.const 66 i32.store8
    i32.const 131078 i32.const 67 i32.store8
    i32.const 131079 i32.const 68 i32.store8
    i32.const 131080 i32.const 69 i32.store8
    i32.const 131081 i32.const 70 i32.store8
    i32.const 131072 i32.const 262144 i32.const 10 i32.const 13
    call $decode i32.const 13 i32.eq call $expect
    i32.const 262144 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262145 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262146 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262147 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262148 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262149 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262150 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262151 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262152 i32.load8_u i32.const 66 i32.eq call $expect
    i32.const 262153 i32.load8_u i32.const 67 i32.eq call $expect
    i32.const 262154 i32.load8_u i32.const 68 i32.eq call $expect
    i32.const 262155 i32.load8_u i32.const 69 i32.eq call $expect
    i32.const 262156 i32.load8_u i32.const 70 i32.eq call $expect
    i32.const 131072 i32.load8_u i32.const 19 i32.eq call $expect
    i32.const 131073 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 131074 i32.load8_u i32.const 1 i32.eq call $expect
    i32.const 131075 i32.load8_u i32.const 0 i32.eq call $expect
    i32.const 131076 i32.load8_u i32.const 80 i32.eq call $expect
    i32.const 131077 i32.load8_u i32.const 66 i32.eq call $expect
    i32.const 131078 i32.load8_u i32.const 67 i32.eq call $expect
    i32.const 131079 i32.load8_u i32.const 68 i32.eq call $expect
    i32.const 131080 i32.load8_u i32.const 69 i32.eq call $expect
    i32.const 131081 i32.load8_u i32.const 70 i32.eq call $expect
    i32.const 131082 i32.const 262144 i32.const 90 call $check_fill
    i32.const 262157 i32.const 2097152 i32.const 90 call $check_fill
    ;; hot_overlap
    i32.const 131072 i32.const 90 i32.const 1966080 memory.fill
    i32.const 262144 i32.const 165 i32.const 64 memory.fill
    i32.const 131072 i32.const 19 i32.store8
    i32.const 131073 i32.const 65 i32.store8
    i32.const 131074 i32.const 1 i32.store8
    i32.const 131075 i32.const 0 i32.store8
    i32.const 131076 i32.const 224 i32.store8
    i32.const 131077 i32.const 66 i32.store8
    i32.const 131078 i32.const 67 i32.store8
    i32.const 131079 i32.const 68 i32.store8
    i32.const 131080 i32.const 69 i32.store8
    i32.const 131081 i32.const 70 i32.store8
    i32.const 131082 i32.const 71 i32.store8
    i32.const 131083 i32.const 72 i32.store8
    i32.const 131084 i32.const 73 i32.store8
    i32.const 131085 i32.const 74 i32.store8
    i32.const 131086 i32.const 75 i32.store8
    i32.const 131087 i32.const 76 i32.store8
    i32.const 131088 i32.const 77 i32.store8
    i32.const 131089 i32.const 78 i32.store8
    i32.const 131090 i32.const 79 i32.store8
    i32.const 131072 i32.const 262144 i32.const 19 i32.const 64
    call $decode i32.const 22 i32.eq call $expect
    i32.const 262144 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262145 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262146 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262147 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262148 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262149 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262150 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262151 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262152 i32.load8_u i32.const 66 i32.eq call $expect
    i32.const 262153 i32.load8_u i32.const 67 i32.eq call $expect
    i32.const 262154 i32.load8_u i32.const 68 i32.eq call $expect
    i32.const 262155 i32.load8_u i32.const 69 i32.eq call $expect
    i32.const 262156 i32.load8_u i32.const 70 i32.eq call $expect
    i32.const 262157 i32.load8_u i32.const 71 i32.eq call $expect
    i32.const 262158 i32.load8_u i32.const 72 i32.eq call $expect
    i32.const 262159 i32.load8_u i32.const 73 i32.eq call $expect
    i32.const 262160 i32.load8_u i32.const 74 i32.eq call $expect
    i32.const 262161 i32.load8_u i32.const 75 i32.eq call $expect
    i32.const 262162 i32.load8_u i32.const 76 i32.eq call $expect
    i32.const 262163 i32.load8_u i32.const 77 i32.eq call $expect
    i32.const 262164 i32.load8_u i32.const 78 i32.eq call $expect
    i32.const 262165 i32.load8_u i32.const 79 i32.eq call $expect
    i32.const 131072 i32.load8_u i32.const 19 i32.eq call $expect
    i32.const 131073 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 131074 i32.load8_u i32.const 1 i32.eq call $expect
    i32.const 131075 i32.load8_u i32.const 0 i32.eq call $expect
    i32.const 131076 i32.load8_u i32.const 224 i32.eq call $expect
    i32.const 131077 i32.load8_u i32.const 66 i32.eq call $expect
    i32.const 131078 i32.load8_u i32.const 67 i32.eq call $expect
    i32.const 131079 i32.load8_u i32.const 68 i32.eq call $expect
    i32.const 131080 i32.load8_u i32.const 69 i32.eq call $expect
    i32.const 131081 i32.load8_u i32.const 70 i32.eq call $expect
    i32.const 131082 i32.load8_u i32.const 71 i32.eq call $expect
    i32.const 131083 i32.load8_u i32.const 72 i32.eq call $expect
    i32.const 131084 i32.load8_u i32.const 73 i32.eq call $expect
    i32.const 131085 i32.load8_u i32.const 74 i32.eq call $expect
    i32.const 131086 i32.load8_u i32.const 75 i32.eq call $expect
    i32.const 131087 i32.load8_u i32.const 76 i32.eq call $expect
    i32.const 131088 i32.load8_u i32.const 77 i32.eq call $expect
    i32.const 131089 i32.load8_u i32.const 78 i32.eq call $expect
    i32.const 131090 i32.load8_u i32.const 79 i32.eq call $expect
    i32.const 131091 i32.const 262144 i32.const 90 call $check_fill
    i32.const 262208 i32.const 2097152 i32.const 90 call $check_fill
    ;; hot_snapshot18
    i32.const 131072 i32.const 90 i32.const 1966080 memory.fill
    i32.const 262144 i32.const 165 i32.const 64 memory.fill
    i32.const 131072 i32.const 64 i32.store8
    i32.const 131073 i32.const 65 i32.store8
    i32.const 131074 i32.const 66 i32.store8
    i32.const 131075 i32.const 67 i32.store8
    i32.const 131076 i32.const 68 i32.store8
    i32.const 131077 i32.const 4 i32.store8
    i32.const 131078 i32.const 0 i32.store8
    i32.const 131079 i32.const 224 i32.store8
    i32.const 131080 i32.const 70 i32.store8
    i32.const 131081 i32.const 71 i32.store8
    i32.const 131082 i32.const 72 i32.store8
    i32.const 131083 i32.const 73 i32.store8
    i32.const 131084 i32.const 74 i32.store8
    i32.const 131085 i32.const 75 i32.store8
    i32.const 131086 i32.const 76 i32.store8
    i32.const 131087 i32.const 77 i32.store8
    i32.const 131088 i32.const 78 i32.store8
    i32.const 131089 i32.const 79 i32.store8
    i32.const 131090 i32.const 80 i32.store8
    i32.const 131091 i32.const 81 i32.store8
    i32.const 131092 i32.const 82 i32.store8
    i32.const 131093 i32.const 83 i32.store8
    i32.const 131072 i32.const 262144 i32.const 22 i32.const 64
    call $decode i32.const 22 i32.eq call $expect
    i32.const 262144 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262145 i32.load8_u i32.const 66 i32.eq call $expect
    i32.const 262146 i32.load8_u i32.const 67 i32.eq call $expect
    i32.const 262147 i32.load8_u i32.const 68 i32.eq call $expect
    i32.const 262148 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262149 i32.load8_u i32.const 66 i32.eq call $expect
    i32.const 262150 i32.load8_u i32.const 67 i32.eq call $expect
    i32.const 262151 i32.load8_u i32.const 68 i32.eq call $expect
    i32.const 262152 i32.load8_u i32.const 70 i32.eq call $expect
    i32.const 262153 i32.load8_u i32.const 71 i32.eq call $expect
    i32.const 262154 i32.load8_u i32.const 72 i32.eq call $expect
    i32.const 262155 i32.load8_u i32.const 73 i32.eq call $expect
    i32.const 262156 i32.load8_u i32.const 74 i32.eq call $expect
    i32.const 262157 i32.load8_u i32.const 75 i32.eq call $expect
    i32.const 262158 i32.load8_u i32.const 76 i32.eq call $expect
    i32.const 262159 i32.load8_u i32.const 77 i32.eq call $expect
    i32.const 262160 i32.load8_u i32.const 78 i32.eq call $expect
    i32.const 262161 i32.load8_u i32.const 79 i32.eq call $expect
    i32.const 262162 i32.load8_u i32.const 80 i32.eq call $expect
    i32.const 262163 i32.load8_u i32.const 81 i32.eq call $expect
    i32.const 262164 i32.load8_u i32.const 82 i32.eq call $expect
    i32.const 262165 i32.load8_u i32.const 83 i32.eq call $expect
    i32.const 131072 i32.load8_u i32.const 64 i32.eq call $expect
    i32.const 131073 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 131074 i32.load8_u i32.const 66 i32.eq call $expect
    i32.const 131075 i32.load8_u i32.const 67 i32.eq call $expect
    i32.const 131076 i32.load8_u i32.const 68 i32.eq call $expect
    i32.const 131077 i32.load8_u i32.const 4 i32.eq call $expect
    i32.const 131078 i32.load8_u i32.const 0 i32.eq call $expect
    i32.const 131079 i32.load8_u i32.const 224 i32.eq call $expect
    i32.const 131080 i32.load8_u i32.const 70 i32.eq call $expect
    i32.const 131081 i32.load8_u i32.const 71 i32.eq call $expect
    i32.const 131082 i32.load8_u i32.const 72 i32.eq call $expect
    i32.const 131083 i32.load8_u i32.const 73 i32.eq call $expect
    i32.const 131084 i32.load8_u i32.const 74 i32.eq call $expect
    i32.const 131085 i32.load8_u i32.const 75 i32.eq call $expect
    i32.const 131086 i32.load8_u i32.const 76 i32.eq call $expect
    i32.const 131087 i32.load8_u i32.const 77 i32.eq call $expect
    i32.const 131088 i32.load8_u i32.const 78 i32.eq call $expect
    i32.const 131089 i32.load8_u i32.const 79 i32.eq call $expect
    i32.const 131090 i32.load8_u i32.const 80 i32.eq call $expect
    i32.const 131091 i32.load8_u i32.const 81 i32.eq call $expect
    i32.const 131092 i32.load8_u i32.const 82 i32.eq call $expect
    i32.const 131093 i32.load8_u i32.const 83 i32.eq call $expect
    i32.const 131094 i32.const 262144 i32.const 90 call $check_fill
    i32.const 262208 i32.const 2097152 i32.const 90 call $check_fill
    ;; slow_snapshot32
    i32.const 131072 i32.const 90 i32.const 1966080 memory.fill
    i32.const 262144 i32.const 165 i32.const 100 memory.fill
    i32.const 131072 i32.const 255 i32.store8
    i32.const 131073 i32.const 4 i32.store8
    i32.const 131074 i32.const 65 i32.store8
    i32.const 131075 i32.const 66 i32.store8
    i32.const 131076 i32.const 67 i32.store8
    i32.const 131077 i32.const 68 i32.store8
    i32.const 131078 i32.const 69 i32.store8
    i32.const 131079 i32.const 70 i32.store8
    i32.const 131080 i32.const 71 i32.store8
    i32.const 131081 i32.const 72 i32.store8
    i32.const 131082 i32.const 73 i32.store8
    i32.const 131083 i32.const 74 i32.store8
    i32.const 131084 i32.const 75 i32.store8
    i32.const 131085 i32.const 76 i32.store8
    i32.const 131086 i32.const 77 i32.store8
    i32.const 131087 i32.const 78 i32.store8
    i32.const 131088 i32.const 79 i32.store8
    i32.const 131089 i32.const 80 i32.store8
    i32.const 131090 i32.const 81 i32.store8
    i32.const 131091 i32.const 82 i32.store8
    i32.const 131092 i32.const 83 i32.store8
    i32.const 131093 i32.const 19 i32.store8
    i32.const 131094 i32.const 0 i32.store8
    i32.const 131095 i32.const 0 i32.store8
    i32.const 131096 i32.const 80 i32.store8
    i32.const 131097 i32.const 90 i32.store8
    i32.const 131098 i32.const 91 i32.store8
    i32.const 131099 i32.const 92 i32.store8
    i32.const 131100 i32.const 93 i32.store8
    i32.const 131101 i32.const 94 i32.store8
    i32.const 131072 i32.const 262144 i32.const 30 i32.const 100
    call $decode i32.const 43 i32.eq call $expect
    i32.const 262144 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262145 i32.load8_u i32.const 66 i32.eq call $expect
    i32.const 262146 i32.load8_u i32.const 67 i32.eq call $expect
    i32.const 262147 i32.load8_u i32.const 68 i32.eq call $expect
    i32.const 262148 i32.load8_u i32.const 69 i32.eq call $expect
    i32.const 262149 i32.load8_u i32.const 70 i32.eq call $expect
    i32.const 262150 i32.load8_u i32.const 71 i32.eq call $expect
    i32.const 262151 i32.load8_u i32.const 72 i32.eq call $expect
    i32.const 262152 i32.load8_u i32.const 73 i32.eq call $expect
    i32.const 262153 i32.load8_u i32.const 74 i32.eq call $expect
    i32.const 262154 i32.load8_u i32.const 75 i32.eq call $expect
    i32.const 262155 i32.load8_u i32.const 76 i32.eq call $expect
    i32.const 262156 i32.load8_u i32.const 77 i32.eq call $expect
    i32.const 262157 i32.load8_u i32.const 78 i32.eq call $expect
    i32.const 262158 i32.load8_u i32.const 79 i32.eq call $expect
    i32.const 262159 i32.load8_u i32.const 80 i32.eq call $expect
    i32.const 262160 i32.load8_u i32.const 81 i32.eq call $expect
    i32.const 262161 i32.load8_u i32.const 82 i32.eq call $expect
    i32.const 262162 i32.load8_u i32.const 83 i32.eq call $expect
    i32.const 262163 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262164 i32.load8_u i32.const 66 i32.eq call $expect
    i32.const 262165 i32.load8_u i32.const 67 i32.eq call $expect
    i32.const 262166 i32.load8_u i32.const 68 i32.eq call $expect
    i32.const 262167 i32.load8_u i32.const 69 i32.eq call $expect
    i32.const 262168 i32.load8_u i32.const 70 i32.eq call $expect
    i32.const 262169 i32.load8_u i32.const 71 i32.eq call $expect
    i32.const 262170 i32.load8_u i32.const 72 i32.eq call $expect
    i32.const 262171 i32.load8_u i32.const 73 i32.eq call $expect
    i32.const 262172 i32.load8_u i32.const 74 i32.eq call $expect
    i32.const 262173 i32.load8_u i32.const 75 i32.eq call $expect
    i32.const 262174 i32.load8_u i32.const 76 i32.eq call $expect
    i32.const 262175 i32.load8_u i32.const 77 i32.eq call $expect
    i32.const 262176 i32.load8_u i32.const 78 i32.eq call $expect
    i32.const 262177 i32.load8_u i32.const 79 i32.eq call $expect
    i32.const 262178 i32.load8_u i32.const 80 i32.eq call $expect
    i32.const 262179 i32.load8_u i32.const 81 i32.eq call $expect
    i32.const 262180 i32.load8_u i32.const 82 i32.eq call $expect
    i32.const 262181 i32.load8_u i32.const 83 i32.eq call $expect
    i32.const 262182 i32.load8_u i32.const 90 i32.eq call $expect
    i32.const 262183 i32.load8_u i32.const 91 i32.eq call $expect
    i32.const 262184 i32.load8_u i32.const 92 i32.eq call $expect
    i32.const 262185 i32.load8_u i32.const 93 i32.eq call $expect
    i32.const 262186 i32.load8_u i32.const 94 i32.eq call $expect
    i32.const 131072 i32.load8_u i32.const 255 i32.eq call $expect
    i32.const 131073 i32.load8_u i32.const 4 i32.eq call $expect
    i32.const 131074 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 131075 i32.load8_u i32.const 66 i32.eq call $expect
    i32.const 131076 i32.load8_u i32.const 67 i32.eq call $expect
    i32.const 131077 i32.load8_u i32.const 68 i32.eq call $expect
    i32.const 131078 i32.load8_u i32.const 69 i32.eq call $expect
    i32.const 131079 i32.load8_u i32.const 70 i32.eq call $expect
    i32.const 131080 i32.load8_u i32.const 71 i32.eq call $expect
    i32.const 131081 i32.load8_u i32.const 72 i32.eq call $expect
    i32.const 131082 i32.load8_u i32.const 73 i32.eq call $expect
    i32.const 131083 i32.load8_u i32.const 74 i32.eq call $expect
    i32.const 131084 i32.load8_u i32.const 75 i32.eq call $expect
    i32.const 131085 i32.load8_u i32.const 76 i32.eq call $expect
    i32.const 131086 i32.load8_u i32.const 77 i32.eq call $expect
    i32.const 131087 i32.load8_u i32.const 78 i32.eq call $expect
    i32.const 131088 i32.load8_u i32.const 79 i32.eq call $expect
    i32.const 131089 i32.load8_u i32.const 80 i32.eq call $expect
    i32.const 131090 i32.load8_u i32.const 81 i32.eq call $expect
    i32.const 131091 i32.load8_u i32.const 82 i32.eq call $expect
    i32.const 131092 i32.load8_u i32.const 83 i32.eq call $expect
    i32.const 131093 i32.load8_u i32.const 19 i32.eq call $expect
    i32.const 131094 i32.load8_u i32.const 0 i32.eq call $expect
    i32.const 131095 i32.load8_u i32.const 0 i32.eq call $expect
    i32.const 131096 i32.load8_u i32.const 80 i32.eq call $expect
    i32.const 131097 i32.load8_u i32.const 90 i32.eq call $expect
    i32.const 131098 i32.load8_u i32.const 91 i32.eq call $expect
    i32.const 131099 i32.load8_u i32.const 92 i32.eq call $expect
    i32.const 131100 i32.load8_u i32.const 93 i32.eq call $expect
    i32.const 131101 i32.load8_u i32.const 94 i32.eq call $expect
    i32.const 131102 i32.const 262144 i32.const 90 call $check_fill
    i32.const 262244 i32.const 2097152 i32.const 90 call $check_fill
    ;; slow_snapshot64
    i32.const 131072 i32.const 90 i32.const 1966080 memory.fill
    i32.const 262144 i32.const 165 i32.const 110 memory.fill
    i32.const 131072 i32.const 255 i32.store8
    i32.const 131073 i32.const 18 i32.store8
    i32.const 131074 i32.const 65 i32.store8
    i32.const 131075 i32.const 66 i32.store8
    i32.const 131076 i32.const 67 i32.store8
    i32.const 131077 i32.const 68 i32.store8
    i32.const 131078 i32.const 69 i32.store8
    i32.const 131079 i32.const 70 i32.store8
    i32.const 131080 i32.const 71 i32.store8
    i32.const 131081 i32.const 72 i32.store8
    i32.const 131082 i32.const 73 i32.store8
    i32.const 131083 i32.const 74 i32.store8
    i32.const 131084 i32.const 75 i32.store8
    i32.const 131085 i32.const 76 i32.store8
    i32.const 131086 i32.const 77 i32.store8
    i32.const 131087 i32.const 78 i32.store8
    i32.const 131088 i32.const 79 i32.store8
    i32.const 131089 i32.const 80 i32.store8
    i32.const 131090 i32.const 81 i32.store8
    i32.const 131091 i32.const 82 i32.store8
    i32.const 131092 i32.const 83 i32.store8
    i32.const 131093 i32.const 84 i32.store8
    i32.const 131094 i32.const 85 i32.store8
    i32.const 131095 i32.const 86 i32.store8
    i32.const 131096 i32.const 87 i32.store8
    i32.const 131097 i32.const 88 i32.store8
    i32.const 131098 i32.const 89 i32.store8
    i32.const 131099 i32.const 90 i32.store8
    i32.const 131100 i32.const 91 i32.store8
    i32.const 131101 i32.const 92 i32.store8
    i32.const 131102 i32.const 93 i32.store8
    i32.const 131103 i32.const 94 i32.store8
    i32.const 131104 i32.const 95 i32.store8
    i32.const 131105 i32.const 96 i32.store8
    i32.const 131106 i32.const 97 i32.store8
    i32.const 131107 i32.const 33 i32.store8
    i32.const 131108 i32.const 0 i32.store8
    i32.const 131109 i32.const 14 i32.store8
    i32.const 131110 i32.const 80 i32.store8
    i32.const 131111 i32.const 100 i32.store8
    i32.const 131112 i32.const 101 i32.store8
    i32.const 131113 i32.const 102 i32.store8
    i32.const 131114 i32.const 103 i32.store8
    i32.const 131115 i32.const 104 i32.store8
    i32.const 131072 i32.const 262144 i32.const 44 i32.const 110
    call $decode i32.const 71 i32.eq call $expect
    i32.const 262144 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262145 i32.load8_u i32.const 66 i32.eq call $expect
    i32.const 262146 i32.load8_u i32.const 67 i32.eq call $expect
    i32.const 262147 i32.load8_u i32.const 68 i32.eq call $expect
    i32.const 262148 i32.load8_u i32.const 69 i32.eq call $expect
    i32.const 262149 i32.load8_u i32.const 70 i32.eq call $expect
    i32.const 262150 i32.load8_u i32.const 71 i32.eq call $expect
    i32.const 262151 i32.load8_u i32.const 72 i32.eq call $expect
    i32.const 262152 i32.load8_u i32.const 73 i32.eq call $expect
    i32.const 262153 i32.load8_u i32.const 74 i32.eq call $expect
    i32.const 262154 i32.load8_u i32.const 75 i32.eq call $expect
    i32.const 262155 i32.load8_u i32.const 76 i32.eq call $expect
    i32.const 262156 i32.load8_u i32.const 77 i32.eq call $expect
    i32.const 262157 i32.load8_u i32.const 78 i32.eq call $expect
    i32.const 262158 i32.load8_u i32.const 79 i32.eq call $expect
    i32.const 262159 i32.load8_u i32.const 80 i32.eq call $expect
    i32.const 262160 i32.load8_u i32.const 81 i32.eq call $expect
    i32.const 262161 i32.load8_u i32.const 82 i32.eq call $expect
    i32.const 262162 i32.load8_u i32.const 83 i32.eq call $expect
    i32.const 262163 i32.load8_u i32.const 84 i32.eq call $expect
    i32.const 262164 i32.load8_u i32.const 85 i32.eq call $expect
    i32.const 262165 i32.load8_u i32.const 86 i32.eq call $expect
    i32.const 262166 i32.load8_u i32.const 87 i32.eq call $expect
    i32.const 262167 i32.load8_u i32.const 88 i32.eq call $expect
    i32.const 262168 i32.load8_u i32.const 89 i32.eq call $expect
    i32.const 262169 i32.load8_u i32.const 90 i32.eq call $expect
    i32.const 262170 i32.load8_u i32.const 91 i32.eq call $expect
    i32.const 262171 i32.load8_u i32.const 92 i32.eq call $expect
    i32.const 262172 i32.load8_u i32.const 93 i32.eq call $expect
    i32.const 262173 i32.load8_u i32.const 94 i32.eq call $expect
    i32.const 262174 i32.load8_u i32.const 95 i32.eq call $expect
    i32.const 262175 i32.load8_u i32.const 96 i32.eq call $expect
    i32.const 262176 i32.load8_u i32.const 97 i32.eq call $expect
    i32.const 262177 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262178 i32.load8_u i32.const 66 i32.eq call $expect
    i32.const 262179 i32.load8_u i32.const 67 i32.eq call $expect
    i32.const 262180 i32.load8_u i32.const 68 i32.eq call $expect
    i32.const 262181 i32.load8_u i32.const 69 i32.eq call $expect
    i32.const 262182 i32.load8_u i32.const 70 i32.eq call $expect
    i32.const 262183 i32.load8_u i32.const 71 i32.eq call $expect
    i32.const 262184 i32.load8_u i32.const 72 i32.eq call $expect
    i32.const 262185 i32.load8_u i32.const 73 i32.eq call $expect
    i32.const 262186 i32.load8_u i32.const 74 i32.eq call $expect
    i32.const 262187 i32.load8_u i32.const 75 i32.eq call $expect
    i32.const 262188 i32.load8_u i32.const 76 i32.eq call $expect
    i32.const 262189 i32.load8_u i32.const 77 i32.eq call $expect
    i32.const 262190 i32.load8_u i32.const 78 i32.eq call $expect
    i32.const 262191 i32.load8_u i32.const 79 i32.eq call $expect
    i32.const 262192 i32.load8_u i32.const 80 i32.eq call $expect
    i32.const 262193 i32.load8_u i32.const 81 i32.eq call $expect
    i32.const 262194 i32.load8_u i32.const 82 i32.eq call $expect
    i32.const 262195 i32.load8_u i32.const 83 i32.eq call $expect
    i32.const 262196 i32.load8_u i32.const 84 i32.eq call $expect
    i32.const 262197 i32.load8_u i32.const 85 i32.eq call $expect
    i32.const 262198 i32.load8_u i32.const 86 i32.eq call $expect
    i32.const 262199 i32.load8_u i32.const 87 i32.eq call $expect
    i32.const 262200 i32.load8_u i32.const 88 i32.eq call $expect
    i32.const 262201 i32.load8_u i32.const 89 i32.eq call $expect
    i32.const 262202 i32.load8_u i32.const 90 i32.eq call $expect
    i32.const 262203 i32.load8_u i32.const 91 i32.eq call $expect
    i32.const 262204 i32.load8_u i32.const 92 i32.eq call $expect
    i32.const 262205 i32.load8_u i32.const 93 i32.eq call $expect
    i32.const 262206 i32.load8_u i32.const 94 i32.eq call $expect
    i32.const 262207 i32.load8_u i32.const 95 i32.eq call $expect
    i32.const 262208 i32.load8_u i32.const 96 i32.eq call $expect
    i32.const 262209 i32.load8_u i32.const 97 i32.eq call $expect
    i32.const 262210 i32.load8_u i32.const 100 i32.eq call $expect
    i32.const 262211 i32.load8_u i32.const 101 i32.eq call $expect
    i32.const 262212 i32.load8_u i32.const 102 i32.eq call $expect
    i32.const 262213 i32.load8_u i32.const 103 i32.eq call $expect
    i32.const 262214 i32.load8_u i32.const 104 i32.eq call $expect
    i32.const 131072 i32.load8_u i32.const 255 i32.eq call $expect
    i32.const 131073 i32.load8_u i32.const 18 i32.eq call $expect
    i32.const 131074 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 131075 i32.load8_u i32.const 66 i32.eq call $expect
    i32.const 131076 i32.load8_u i32.const 67 i32.eq call $expect
    i32.const 131077 i32.load8_u i32.const 68 i32.eq call $expect
    i32.const 131078 i32.load8_u i32.const 69 i32.eq call $expect
    i32.const 131079 i32.load8_u i32.const 70 i32.eq call $expect
    i32.const 131080 i32.load8_u i32.const 71 i32.eq call $expect
    i32.const 131081 i32.load8_u i32.const 72 i32.eq call $expect
    i32.const 131082 i32.load8_u i32.const 73 i32.eq call $expect
    i32.const 131083 i32.load8_u i32.const 74 i32.eq call $expect
    i32.const 131084 i32.load8_u i32.const 75 i32.eq call $expect
    i32.const 131085 i32.load8_u i32.const 76 i32.eq call $expect
    i32.const 131086 i32.load8_u i32.const 77 i32.eq call $expect
    i32.const 131087 i32.load8_u i32.const 78 i32.eq call $expect
    i32.const 131088 i32.load8_u i32.const 79 i32.eq call $expect
    i32.const 131089 i32.load8_u i32.const 80 i32.eq call $expect
    i32.const 131090 i32.load8_u i32.const 81 i32.eq call $expect
    i32.const 131091 i32.load8_u i32.const 82 i32.eq call $expect
    i32.const 131092 i32.load8_u i32.const 83 i32.eq call $expect
    i32.const 131093 i32.load8_u i32.const 84 i32.eq call $expect
    i32.const 131094 i32.load8_u i32.const 85 i32.eq call $expect
    i32.const 131095 i32.load8_u i32.const 86 i32.eq call $expect
    i32.const 131096 i32.load8_u i32.const 87 i32.eq call $expect
    i32.const 131097 i32.load8_u i32.const 88 i32.eq call $expect
    i32.const 131098 i32.load8_u i32.const 89 i32.eq call $expect
    i32.const 131099 i32.load8_u i32.const 90 i32.eq call $expect
    i32.const 131100 i32.load8_u i32.const 91 i32.eq call $expect
    i32.const 131101 i32.load8_u i32.const 92 i32.eq call $expect
    i32.const 131102 i32.load8_u i32.const 93 i32.eq call $expect
    i32.const 131103 i32.load8_u i32.const 94 i32.eq call $expect
    i32.const 131104 i32.load8_u i32.const 95 i32.eq call $expect
    i32.const 131105 i32.load8_u i32.const 96 i32.eq call $expect
    i32.const 131106 i32.load8_u i32.const 97 i32.eq call $expect
    i32.const 131107 i32.load8_u i32.const 33 i32.eq call $expect
    i32.const 131108 i32.load8_u i32.const 0 i32.eq call $expect
    i32.const 131109 i32.load8_u i32.const 14 i32.eq call $expect
    i32.const 131110 i32.load8_u i32.const 80 i32.eq call $expect
    i32.const 131111 i32.load8_u i32.const 100 i32.eq call $expect
    i32.const 131112 i32.load8_u i32.const 101 i32.eq call $expect
    i32.const 131113 i32.load8_u i32.const 102 i32.eq call $expect
    i32.const 131114 i32.load8_u i32.const 103 i32.eq call $expect
    i32.const 131115 i32.load8_u i32.const 104 i32.eq call $expect
    i32.const 131116 i32.const 262144 i32.const 90 call $check_fill
    i32.const 262254 i32.const 2097152 i32.const 90 call $check_fill
    ;; extended_literals
    i32.const 131072 i32.const 90 i32.const 1966080 memory.fill
    i32.const 262144 i32.const 165 i32.const 16 memory.fill
    i32.const 131072 i32.const 240 i32.store8
    i32.const 131073 i32.const 1 i32.store8
    i32.const 131074 i32.const 65 i32.store8
    i32.const 131075 i32.const 66 i32.store8
    i32.const 131076 i32.const 67 i32.store8
    i32.const 131077 i32.const 68 i32.store8
    i32.const 131078 i32.const 69 i32.store8
    i32.const 131079 i32.const 70 i32.store8
    i32.const 131080 i32.const 71 i32.store8
    i32.const 131081 i32.const 72 i32.store8
    i32.const 131082 i32.const 73 i32.store8
    i32.const 131083 i32.const 74 i32.store8
    i32.const 131084 i32.const 75 i32.store8
    i32.const 131085 i32.const 76 i32.store8
    i32.const 131086 i32.const 77 i32.store8
    i32.const 131087 i32.const 78 i32.store8
    i32.const 131088 i32.const 79 i32.store8
    i32.const 131089 i32.const 80 i32.store8
    i32.const 131072 i32.const 262144 i32.const 18 i32.const 16
    call $decode i32.const 16 i32.eq call $expect
    i32.const 262144 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262145 i32.load8_u i32.const 66 i32.eq call $expect
    i32.const 262146 i32.load8_u i32.const 67 i32.eq call $expect
    i32.const 262147 i32.load8_u i32.const 68 i32.eq call $expect
    i32.const 262148 i32.load8_u i32.const 69 i32.eq call $expect
    i32.const 262149 i32.load8_u i32.const 70 i32.eq call $expect
    i32.const 262150 i32.load8_u i32.const 71 i32.eq call $expect
    i32.const 262151 i32.load8_u i32.const 72 i32.eq call $expect
    i32.const 262152 i32.load8_u i32.const 73 i32.eq call $expect
    i32.const 262153 i32.load8_u i32.const 74 i32.eq call $expect
    i32.const 262154 i32.load8_u i32.const 75 i32.eq call $expect
    i32.const 262155 i32.load8_u i32.const 76 i32.eq call $expect
    i32.const 262156 i32.load8_u i32.const 77 i32.eq call $expect
    i32.const 262157 i32.load8_u i32.const 78 i32.eq call $expect
    i32.const 262158 i32.load8_u i32.const 79 i32.eq call $expect
    i32.const 262159 i32.load8_u i32.const 80 i32.eq call $expect
    i32.const 131072 i32.load8_u i32.const 240 i32.eq call $expect
    i32.const 131073 i32.load8_u i32.const 1 i32.eq call $expect
    i32.const 131074 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 131075 i32.load8_u i32.const 66 i32.eq call $expect
    i32.const 131076 i32.load8_u i32.const 67 i32.eq call $expect
    i32.const 131077 i32.load8_u i32.const 68 i32.eq call $expect
    i32.const 131078 i32.load8_u i32.const 69 i32.eq call $expect
    i32.const 131079 i32.load8_u i32.const 70 i32.eq call $expect
    i32.const 131080 i32.load8_u i32.const 71 i32.eq call $expect
    i32.const 131081 i32.load8_u i32.const 72 i32.eq call $expect
    i32.const 131082 i32.load8_u i32.const 73 i32.eq call $expect
    i32.const 131083 i32.load8_u i32.const 74 i32.eq call $expect
    i32.const 131084 i32.load8_u i32.const 75 i32.eq call $expect
    i32.const 131085 i32.load8_u i32.const 76 i32.eq call $expect
    i32.const 131086 i32.load8_u i32.const 77 i32.eq call $expect
    i32.const 131087 i32.load8_u i32.const 78 i32.eq call $expect
    i32.const 131088 i32.load8_u i32.const 79 i32.eq call $expect
    i32.const 131089 i32.load8_u i32.const 80 i32.eq call $expect
    i32.const 131090 i32.const 262144 i32.const 90 call $check_fill
    i32.const 262160 i32.const 2097152 i32.const 90 call $check_fill
    ;; relaxed_end
    i32.const 131072 i32.const 90 i32.const 1966080 memory.fill
    i32.const 262144 i32.const 165 i32.const 5 memory.fill
    i32.const 131072 i32.const 16 i32.store8
    i32.const 131073 i32.const 65 i32.store8
    i32.const 131074 i32.const 1 i32.store8
    i32.const 131075 i32.const 0 i32.store8
    i32.const 131076 i32.const 0 i32.store8
    i32.const 131072 i32.const 262144 i32.const 5 i32.const 5
    call $decode i32.const 5 i32.eq call $expect
    i32.const 262144 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262145 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262146 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262147 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 262148 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 131072 i32.load8_u i32.const 16 i32.eq call $expect
    i32.const 131073 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 131074 i32.load8_u i32.const 1 i32.eq call $expect
    i32.const 131075 i32.load8_u i32.const 0 i32.eq call $expect
    i32.const 131076 i32.load8_u i32.const 0 i32.eq call $expect
    i32.const 131077 i32.const 262144 i32.const 90 call $check_fill
    i32.const 262149 i32.const 2097152 i32.const 90 call $check_fill
    ;; zero_offset
    i32.const 131072 i32.const 90 i32.const 1966080 memory.fill
    i32.const 262144 i32.const 165 i32.const 32 memory.fill
    i32.const 131072 i32.const 16 i32.store8
    i32.const 131073 i32.const 65 i32.store8
    i32.const 131074 i32.const 0 i32.store8
    i32.const 131075 i32.const 0 i32.store8
    i32.const 131076 i32.const 80 i32.store8
    i32.const 131077 i32.const 66 i32.store8
    i32.const 131078 i32.const 67 i32.store8
    i32.const 131079 i32.const 68 i32.store8
    i32.const 131080 i32.const 69 i32.store8
    i32.const 131081 i32.const 70 i32.store8
    i32.const 131072 i32.const 262144 i32.const 10 i32.const 32
    call $decode i32.const -1 i32.eq call $expect
    i32.const 131072 i32.load8_u i32.const 16 i32.eq call $expect
    i32.const 131073 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 131074 i32.load8_u i32.const 0 i32.eq call $expect
    i32.const 131075 i32.load8_u i32.const 0 i32.eq call $expect
    i32.const 131076 i32.load8_u i32.const 80 i32.eq call $expect
    i32.const 131077 i32.load8_u i32.const 66 i32.eq call $expect
    i32.const 131078 i32.load8_u i32.const 67 i32.eq call $expect
    i32.const 131079 i32.load8_u i32.const 68 i32.eq call $expect
    i32.const 131080 i32.load8_u i32.const 69 i32.eq call $expect
    i32.const 131081 i32.load8_u i32.const 70 i32.eq call $expect
    i32.const 131082 i32.const 262144 i32.const 90 call $check_fill
    i32.const 262176 i32.const 2097152 i32.const 90 call $check_fill
    ;; offset_beyond_prefix
    i32.const 131072 i32.const 90 i32.const 1966080 memory.fill
    i32.const 262144 i32.const 165 i32.const 64 memory.fill
    i32.const 131072 i32.const 0 i32.store8
    i32.const 131073 i32.const 1 i32.store8
    i32.const 131074 i32.const 0 i32.store8
    i32.const 131072 i32.const 262144 i32.const 3 i32.const 64
    call $decode i32.const -1 i32.eq call $expect
    i32.const 131072 i32.load8_u i32.const 0 i32.eq call $expect
    i32.const 131073 i32.load8_u i32.const 1 i32.eq call $expect
    i32.const 131074 i32.load8_u i32.const 0 i32.eq call $expect
    i32.const 131075 i32.const 262144 i32.const 90 call $check_fill
    i32.const 262208 i32.const 2097152 i32.const 90 call $check_fill
    ;; truncated_literal
    i32.const 131072 i32.const 90 i32.const 1966080 memory.fill
    i32.const 262144 i32.const 165 i32.const 32 memory.fill
    i32.const 131072 i32.const 32 i32.store8
    i32.const 131073 i32.const 65 i32.store8
    i32.const 131072 i32.const 262144 i32.const 2 i32.const 32
    call $decode i32.const -1 i32.eq call $expect
    i32.const 131072 i32.load8_u i32.const 32 i32.eq call $expect
    i32.const 131073 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 131074 i32.const 262144 i32.const 90 call $check_fill
    i32.const 262176 i32.const 2097152 i32.const 90 call $check_fill
    ;; truncated_extension
    i32.const 131072 i32.const 90 i32.const 1966080 memory.fill
    i32.const 262144 i32.const 165 i32.const 32 memory.fill
    i32.const 131072 i32.const 240 i32.store8
    i32.const 131073 i32.const 255 i32.store8
    i32.const 131072 i32.const 262144 i32.const 2 i32.const 32
    call $decode i32.const -1 i32.eq call $expect
    i32.const 131072 i32.load8_u i32.const 240 i32.eq call $expect
    i32.const 131073 i32.load8_u i32.const 255 i32.eq call $expect
    i32.const 131074 i32.const 262144 i32.const 90 call $check_fill
    i32.const 262176 i32.const 2097152 i32.const 90 call $check_fill
    ;; truncated_offset
    i32.const 131072 i32.const 90 i32.const 1966080 memory.fill
    i32.const 262144 i32.const 165 i32.const 64 memory.fill
    i32.const 131072 i32.const 16 i32.store8
    i32.const 131073 i32.const 65 i32.store8
    i32.const 131074 i32.const 1 i32.store8
    i32.const 131072 i32.const 262144 i32.const 3 i32.const 64
    call $decode i32.const -1 i32.eq call $expect
    i32.const 131072 i32.load8_u i32.const 16 i32.eq call $expect
    i32.const 131073 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 131074 i32.load8_u i32.const 1 i32.eq call $expect
    i32.const 131075 i32.const 262144 i32.const 90 call $check_fill
    i32.const 262208 i32.const 2097152 i32.const 90 call $check_fill
    ;; output_too_small
    i32.const 131072 i32.const 90 i32.const 1966080 memory.fill
    i32.const 262144 i32.const 165 i32.const 0 memory.fill
    i32.const 131072 i32.const 16 i32.store8
    i32.const 131073 i32.const 65 i32.store8
    i32.const 131072 i32.const 262144 i32.const 2 i32.const 0
    call $decode i32.const -1 i32.eq call $expect
    i32.const 131072 i32.load8_u i32.const 16 i32.eq call $expect
    i32.const 131073 i32.load8_u i32.const 65 i32.eq call $expect
    i32.const 131074 i32.const 262144 i32.const 90 call $check_fill
    i32.const 262144 i32.const 2097152 i32.const 90 call $check_fill
    i32.const 16
  )
)
