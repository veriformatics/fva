import Proofs.Wasm

namespace Artifact
def localCount : Nat := 24
def data : List (Nat × List Nat) := [(65536,[100, 101, 115, 116, 32, 105, 115, 32, 111, 117, 116, 32, 111, 102, 32, 98, 111, 117, 110, 100, 115, 22, 115, 108, 105, 99, 101, 32, 105, 110, 100, 101, 120, 32, 115, 116, 97, 114, 116, 115, 32, 97, 116, 32, 192, 13, 32, 98, 117, 116, 32, 101, 110, 100, 115, 32, 97, 116, 32, 192, 0, 32, 105, 110, 100, 101, 120, 32, 111, 117, 116, 32, 111, 102, 32, 98, 111, 117, 110, 100, 115, 58, 32, 116, 104, 101, 32, 108, 101, 110, 32, 105, 115, 32, 192, 18, 32, 98, 117, 116, 32, 116, 104, 101, 32, 105, 110, 100, 101, 120, 32, 105, 115, 32, 192, 0, 18, 114, 97, 110, 103, 101, 32, 115, 116, 97, 114, 116, 32, 105, 110, 100, 101, 120, 32, 192, 34, 32, 111, 117, 116, 32, 111, 102, 32, 114, 97, 110, 103, 101, 32, 102, 111, 114, 32, 115, 108, 105, 99, 101, 32, 111, 102, 32, 108, 101, 110, 103, 116, 104, 32, 192, 0, 16, 114, 97, 110, 103, 101, 32, 101, 110, 100, 32, 105, 110, 100, 101, 120, 32, 192, 34, 32, 111, 117, 116, 32, 111, 102, 32, 114, 97, 110, 103, 101, 32, 102, 111, 114, 32, 115, 108, 105, 99, 101, 32, 111, 102, 32, 108, 101, 110, 103, 116, 104, 32, 192, 0, 47, 114, 117, 115, 116, 99, 47, 53, 56, 99, 102, 56, 102, 57, 99, 51, 53, 98, 51, 53, 53, 49, 57, 57, 55, 50, 55, 54, 50, 55, 100, 48, 55, 97, 101, 51, 52, 97, 52, 101, 50, 56, 52, 54, 100, 54, 55, 47, 108, 105, 98, 114, 97, 114, 121, 47, 99, 111, 114, 101, 47, 115, 114, 99, 47, 115, 108, 105, 99, 101, 47, 105, 110, 100, 101, 120, 46, 114, 115, 0, 118, 101, 110, 100, 111, 114, 47, 108, 122, 52, 95, 102, 108, 101, 120, 47, 115, 114, 99, 47, 98, 108, 111, 99, 107, 47, 99, 111, 109, 112, 114, 101, 115, 115, 46, 114, 115, 0, 118, 101, 110, 100, 111, 114, 47, 108, 122, 52, 95, 102, 108, 101, 120, 47, 115, 114, 99, 47, 115, 105, 110, 107, 46, 114, 115, 0, 118, 101, 110, 100, 111, 114, 47, 108, 122, 52, 95, 102, 108, 101, 120, 47, 115, 114, 99, 47, 98, 108, 111, 99, 107, 47, 100, 101, 99, 111, 109, 112, 114, 101, 115, 115, 95, 115, 97, 102, 101, 46, 114, 115, 0, 0, 118, 1, 1, 0, 44, 0, 0, 0, 202, 0, 0, 0, 44, 0, 0, 0, 118, 1, 1, 0, 44, 0, 0, 0, 140, 0, 0, 0, 41, 0, 0, 0, 52, 1, 1, 0, 37, 0, 0, 0, 14, 2, 0, 0, 41, 0, 0, 0, 52, 1, 1, 0, 37, 0, 0, 0, 248, 0, 0, 0, 36, 0, 0, 0, 228, 0, 1, 0, 79, 0, 0, 0, 241, 3, 0, 0, 51, 0, 0, 0, 228, 0, 1, 0, 79, 0, 0, 0, 252, 3, 0, 0, 55, 0, 0, 0, 52, 1, 1, 0, 37, 0, 0, 0, 9, 1, 0, 0, 53, 0, 0, 0, 52, 1, 1, 0, 37, 0, 0, 0, 9, 1, 0, 0, 72, 0, 0, 0, 52, 1, 1, 0, 37, 0, 0, 0, 112, 0, 0, 0, 29, 0, 0, 0, 52, 1, 1, 0, 37, 0, 0, 0, 111, 0, 0, 0, 27, 0, 0, 0, 52, 1, 1, 0, 37, 0, 0, 0, 44, 0, 0, 0, 29, 0, 0, 0, 90, 1, 1, 0, 27, 0, 0, 0, 163, 0, 0, 0, 20, 0, 0, 0, 90, 1, 1, 0, 27, 0, 0, 0, 186, 0, 0, 0, 21, 0, 0, 0, 90, 1, 1, 0, 27, 0, 0, 0, 176, 0, 0, 0, 42, 0, 0, 0, 90, 1, 1, 0, 27, 0, 0, 0, 196, 0, 0, 0, 30, 0, 0, 0, 90, 1, 1, 0, 27, 0, 0, 0, 196, 0, 0, 0, 13, 0, 0, 0, 90, 1, 1, 0, 27, 0, 0, 0, 134, 0, 0, 0, 9, 0, 0, 0, 90, 1, 1, 0, 27, 0, 0, 0, 127, 0, 0, 0, 9, 0, 0, 0])]
def code (pc : Nat) : Option Wasm.Instr :=
(if pc < 491 then
(if pc < 245 then
(if pc < 122 then
(if pc < 61 then
(if pc < 30 then
(if pc < 15 then
(if pc < 7 then
(if pc < 3 then
(if pc < 1 then
(if pc = 0 then some (.block 6) else none)
else (if pc < 2 then
(if pc = 1 then some (.get 2) else none)
else (if pc = 2 then some (.brIf 0) else none)))
else (if pc < 5 then
(if pc < 4 then
(if pc = 3 then some (.const 4294967295) else none)
else (if pc = 4 then some (.ret) else none))
else (if pc < 6 then
(if pc = 5 then some (.end) else none)
else (if pc = 6 then some (.const 0) else none))))
else (if pc < 11 then
(if pc < 9 then
(if pc < 8 then
(if pc = 7 then some (.get 3) else none)
else (if pc = 8 then some (.const 4294967262) else none))
else (if pc < 10 then
(if pc = 9 then some (.bin .add) else none)
else (if pc = 10 then some (.tee 4) else none)))
else (if pc < 13 then
(if pc < 12 then
(if pc = 11 then some (.get 4) else none)
else (if pc = 12 then some (.get 3) else none))
else (if pc < 14 then
(if pc = 13 then some (.bin .gt) else none)
else (if pc = 14 then some (.select) else none)))))
else (if pc < 22 then
(if pc < 18 then
(if pc < 16 then
(if pc = 15 then some (.set 5) else none)
else (if pc < 17 then
(if pc = 16 then some (.const 0) else none)
else (if pc = 17 then some (.get 2) else none)))
else (if pc < 20 then
(if pc < 19 then
(if pc = 18 then some (.const 4294967278) else none)
else (if pc = 19 then some (.bin .add) else none))
else (if pc < 21 then
(if pc = 20 then some (.tee 4) else none)
else (if pc = 21 then some (.get 4) else none))))
else (if pc < 26 then
(if pc < 24 then
(if pc < 23 then
(if pc = 22 then some (.get 2) else none)
else (if pc = 23 then some (.bin .gt) else none))
else (if pc < 25 then
(if pc = 24 then some (.select) else none)
else (if pc = 25 then some (.set 6) else none)))
else (if pc < 28 then
(if pc < 27 then
(if pc = 26 then some (.get 3) else none)
else (if pc = 27 then some (.const 4294967264) else none))
else (if pc < 29 then
(if pc = 28 then some (.bin .add) else none)
else (if pc = 29 then some (.set 7) else none))))))
else (if pc < 45 then
(if pc < 37 then
(if pc < 33 then
(if pc < 31 then
(if pc = 30 then some (.get 3) else none)
else (if pc < 32 then
(if pc = 31 then some (.const 4294967232) else none)
else (if pc = 32 then some (.bin .add) else none)))
else (if pc < 35 then
(if pc < 34 then
(if pc = 33 then some (.set 8) else none)
else (if pc = 34 then some (.get 3) else none))
else (if pc < 36 then
(if pc = 35 then some (.const 4294967278) else none)
else (if pc = 36 then some (.bin .add) else none))))
else (if pc < 41 then
(if pc < 39 then
(if pc < 38 then
(if pc = 37 then some (.set 9) else none)
else (if pc = 38 then some (.const 0) else none))
else (if pc < 40 then
(if pc = 39 then some (.set 10) else none)
else (if pc = 40 then some (.const 0) else none)))
else (if pc < 43 then
(if pc < 42 then
(if pc = 41 then some (.set 11) else none)
else (if pc = 42 then some (.block 976) else none))
else (if pc < 44 then
(if pc = 43 then some (.block 969) else none)
else (if pc = 44 then some (.block 962) else none)))))
else (if pc < 53 then
(if pc < 49 then
(if pc < 47 then
(if pc < 46 then
(if pc = 45 then some (.block 956) else none)
else (if pc = 46 then some (.block 949) else none))
else (if pc < 48 then
(if pc = 47 then some (.block 942) else none)
else (if pc = 48 then some (.block 936) else none)))
else (if pc < 51 then
(if pc < 50 then
(if pc = 49 then some (.block 929) else none)
else (if pc = 50 then some (.block 922) else none))
else (if pc < 52 then
(if pc = 51 then some (.block 916) else none)
else (if pc = 52 then some (.block 909) else none))))
else (if pc < 57 then
(if pc < 55 then
(if pc < 54 then
(if pc = 53 then some (.block 903) else none)
else (if pc = 54 then some (.block 900) else none))
else (if pc < 56 then
(if pc = 55 then some (.loop 899) else none)
else (if pc = 56 then some (.get 11) else none)))
else (if pc < 59 then
(if pc < 58 then
(if pc = 57 then some (.const 1) else none)
else (if pc = 58 then some (.bin .add) else none))
else (if pc < 60 then
(if pc = 59 then some (.set 4) else none)
else (if pc = 60 then some (.const 15) else none)))))))
else (if pc < 91 then
(if pc < 76 then
(if pc < 68 then
(if pc < 64 then
(if pc < 62 then
(if pc = 61 then some (.set 12) else none)
else (if pc < 63 then
(if pc = 62 then some (.block 557) else none)
else (if pc = 63 then some (.block 550) else none)))
else (if pc < 66 then
(if pc < 65 then
(if pc = 64 then some (.block 544) else none)
else (if pc = 65 then some (.block 537) else none))
else (if pc < 67 then
(if pc = 66 then some (.block 530) else none)
else (if pc = 67 then some (.block 524) else none))))
else (if pc < 72 then
(if pc < 70 then
(if pc < 69 then
(if pc = 68 then some (.block 517) else none)
else (if pc = 69 then some (.block 510) else none))
else (if pc < 71 then
(if pc = 70 then some (.block 324) else none)
else (if pc = 71 then some (.block 100) else none)))
else (if pc < 74 then
(if pc < 73 then
(if pc = 72 then some (.get 0) else none)
else (if pc = 73 then some (.get 11) else none))
else (if pc < 75 then
(if pc = 74 then some (.bin .add) else none)
else (if pc = 75 then some (.load 1 0) else none)))))
else (if pc < 83 then
(if pc < 79 then
(if pc < 77 then
(if pc = 76 then some (.tee 13) else none)
else (if pc < 78 then
(if pc = 77 then some (.const 15) else none)
else (if pc = 78 then some (.bin .band) else none)))
else (if pc < 81 then
(if pc < 80 then
(if pc = 79 then some (.tee 14) else none)
else (if pc = 80 then some (.const 15) else none))
else (if pc < 82 then
(if pc = 81 then some (.bin .eq) else none)
else (if pc = 82 then some (.brIf 0) else none))))
else (if pc < 87 then
(if pc < 85 then
(if pc < 84 then
(if pc = 83 then some (.block 97) else none)
else (if pc = 84 then some (.get 11) else none))
else (if pc < 86 then
(if pc = 85 then some (.get 6) else none)
else (if pc = 86 then some (.bin .ge) else none)))
else (if pc < 89 then
(if pc < 88 then
(if pc = 87 then some (.brIf 0) else none)
else (if pc = 88 then some (.get 13) else none))
else (if pc < 90 then
(if pc = 89 then some (.const 239) else none)
else (if pc = 90 then some (.bin .gt) else none))))))
else (if pc < 106 then
(if pc < 98 then
(if pc < 94 then
(if pc < 92 then
(if pc = 91 then some (.brIf 0) else none)
else (if pc < 93 then
(if pc = 92 then some (.get 10) else none)
else (if pc = 93 then some (.get 5) else none)))
else (if pc < 96 then
(if pc < 95 then
(if pc = 94 then some (.bin .lt) else none)
else (if pc = 95 then some (.brIf 2) else none))
else (if pc < 97 then
(if pc = 96 then some (.end) else none)
else (if pc = 97 then some (.get 14) else none))))
else (if pc < 102 then
(if pc < 100 then
(if pc < 99 then
(if pc = 98 then some (.set 12) else none)
else (if pc = 99 then some (.end) else none))
else (if pc < 101 then
(if pc = 100 then some (.block 110) else none)
else (if pc = 101 then some (.get 13) else none)))
else (if pc < 104 then
(if pc < 103 then
(if pc = 102 then some (.const 4) else none)
else (if pc = 103 then some (.bin .shr) else none))
else (if pc < 105 then
(if pc = 104 then some (.tee 15) else none)
else (if pc = 105 then some (.brIf 0) else none)))))
else (if pc < 114 then
(if pc < 110 then
(if pc < 108 then
(if pc < 107 then
(if pc = 106 then some (.get 10) else none)
else (if pc = 107 then some (.set 14) else none))
else (if pc < 109 then
(if pc = 108 then some (.br 9) else none)
else (if pc = 109 then some (.end) else none)))
else (if pc < 112 then
(if pc < 111 then
(if pc = 110 then some (.block 154) else none)
else (if pc = 111 then some (.block 120) else none))
else (if pc < 113 then
(if pc = 112 then some (.get 15) else none)
else (if pc = 113 then some (.const 15) else none))))
else (if pc < 118 then
(if pc < 116 then
(if pc < 115 then
(if pc = 114 then some (.bin .eq) else none)
else (if pc = 115 then some (.brIf 0) else none))
else (if pc < 117 then
(if pc = 116 then some (.get 4) else none)
else (if pc = 117 then some (.set 13) else none)))
else (if pc < 120 then
(if pc < 119 then
(if pc = 118 then some (.br 1) else none)
else (if pc = 119 then some (.end) else none))
else (if pc < 121 then
(if pc = 120 then some (.const 0) else none)
else (if pc = 121 then some (.set 15) else none))))))))
else (if pc < 183 then
(if pc < 152 then
(if pc < 137 then
(if pc < 129 then
(if pc < 125 then
(if pc < 123 then
(if pc = 122 then some (.loop 149) else none)
else (if pc < 124 then
(if pc = 123 then some (.block 131) else none)
else (if pc = 124 then some (.get 2) else none)))
else (if pc < 127 then
(if pc < 126 then
(if pc = 125 then some (.get 4) else none)
else (if pc = 126 then some (.bin .ne) else none))
else (if pc < 128 then
(if pc = 127 then some (.brIf 0) else none)
else (if pc = 128 then some (.const 4294967295) else none))))
else (if pc < 133 then
(if pc < 131 then
(if pc < 130 then
(if pc = 129 then some (.ret) else none)
else (if pc = 130 then some (.end) else none))
else (if pc < 132 then
(if pc = 131 then some (.get 15) else none)
else (if pc = 132 then some (.get 0) else none)))
else (if pc < 135 then
(if pc < 134 then
(if pc = 133 then some (.get 4) else none)
else (if pc = 134 then some (.bin .add) else none))
else (if pc < 136 then
(if pc = 135 then some (.load 1 0) else none)
else (if pc = 136 then some (.tee 14) else none)))))
else (if pc < 144 then
(if pc < 140 then
(if pc < 138 then
(if pc = 137 then some (.bin .add) else none)
else (if pc < 139 then
(if pc = 138 then some (.set 15) else none)
else (if pc = 139 then some (.get 4) else none)))
else (if pc < 142 then
(if pc < 141 then
(if pc = 140 then some (.const 1) else none)
else (if pc = 141 then some (.bin .add) else none))
else (if pc < 143 then
(if pc = 142 then some (.tee 13) else none)
else (if pc = 143 then some (.set 4) else none))))
else (if pc < 148 then
(if pc < 146 then
(if pc < 145 then
(if pc = 144 then some (.get 14) else none)
else (if pc = 145 then some (.const 255) else none))
else (if pc < 147 then
(if pc = 146 then some (.bin .eq) else none)
else (if pc = 147 then some (.brIf 0) else none)))
else (if pc < 150 then
(if pc < 149 then
(if pc = 148 then some (.end) else none)
else (if pc = 149 then some (.get 15) else none))
else (if pc < 151 then
(if pc = 150 then some (.const 15) else none)
else (if pc = 151 then some (.bin .add) else none))))))
else (if pc < 167 then
(if pc < 159 then
(if pc < 155 then
(if pc < 153 then
(if pc = 152 then some (.set 15) else none)
else (if pc < 154 then
(if pc = 153 then some (.end) else none)
else (if pc = 154 then some (.const 4294967295) else none)))
else (if pc < 157 then
(if pc < 156 then
(if pc = 155 then some (.set 16) else none)
else (if pc = 156 then some (.get 15) else none))
else (if pc < 158 then
(if pc = 157 then some (.get 2) else none)
else (if pc = 158 then some (.get 13) else none))))
else (if pc < 163 then
(if pc < 161 then
(if pc < 160 then
(if pc = 159 then some (.bin .sub) else none)
else (if pc = 160 then some (.bin .gt) else none))
else (if pc < 162 then
(if pc = 161 then some (.brIf 10) else none)
else (if pc = 162 then some (.get 15) else none)))
else (if pc < 165 then
(if pc < 164 then
(if pc = 163 then some (.get 3) else none)
else (if pc = 164 then some (.get 10) else none))
else (if pc < 166 then
(if pc = 165 then some (.bin .sub) else none)
else (if pc = 166 then some (.bin .gt) else none)))))
else (if pc < 175 then
(if pc < 171 then
(if pc < 169 then
(if pc < 168 then
(if pc = 167 then some (.brIf 10) else none)
else (if pc = 168 then some (.get 15) else none))
else (if pc < 170 then
(if pc = 169 then some (.get 13) else none)
else (if pc = 170 then some (.bin .add) else none)))
else (if pc < 173 then
(if pc < 172 then
(if pc = 171 then some (.tee 4) else none)
else (if pc = 172 then some (.get 15) else none))
else (if pc < 174 then
(if pc = 173 then some (.bin .lt) else none)
else (if pc = 174 then some (.brIf 1) else none))))
else (if pc < 179 then
(if pc < 177 then
(if pc < 176 then
(if pc = 175 then some (.get 4) else none)
else (if pc = 176 then some (.get 2) else none))
else (if pc < 178 then
(if pc = 177 then some (.bin .gt) else none)
else (if pc = 178 then some (.brIf 1) else none)))
else (if pc < 181 then
(if pc < 180 then
(if pc = 179 then some (.block 317) else none)
else (if pc = 180 then some (.get 15) else none))
else (if pc < 182 then
(if pc = 181 then some (.get 10) else none)
else (if pc = 182 then some (.bin .add) else none)))))))
else (if pc < 214 then
(if pc < 198 then
(if pc < 190 then
(if pc < 186 then
(if pc < 184 then
(if pc = 183 then some (.tee 14) else none)
else (if pc < 185 then
(if pc = 184 then some (.get 15) else none)
else (if pc = 185 then some (.bin .lt) else none)))
else (if pc < 188 then
(if pc < 187 then
(if pc = 186 then some (.brIf 0) else none)
else (if pc = 187 then some (.get 14) else none))
else (if pc < 189 then
(if pc = 188 then some (.get 3) else none)
else (if pc = 189 then some (.bin .gt) else none))))
else (if pc < 194 then
(if pc < 192 then
(if pc < 191 then
(if pc = 190 then some (.brIf 0) else none)
else (if pc = 191 then some (.get 15) else none))
else (if pc < 193 then
(if pc = 192 then some (.eqz) else none)
else (if pc = 193 then some (.brIf 9) else none)))
else (if pc < 196 then
(if pc < 195 then
(if pc = 194 then some (.get 0) else none)
else (if pc = 195 then some (.get 13) else none))
else (if pc < 197 then
(if pc = 196 then some (.bin .add) else none)
else (if pc = 197 then some (.set 13) else none)))))
else (if pc < 206 then
(if pc < 202 then
(if pc < 200 then
(if pc < 199 then
(if pc = 198 then some (.get 1) else none)
else (if pc = 199 then some (.get 10) else none))
else (if pc < 201 then
(if pc = 200 then some (.bin .add) else none)
else (if pc = 201 then some (.set 11) else none)))
else (if pc < 204 then
(if pc < 203 then
(if pc = 202 then some (.block 290) else none)
else (if pc = 203 then some (.block 273) else none))
else (if pc < 205 then
(if pc = 204 then some (.block 256) else none)
else (if pc = 205 then some (.block 231) else none))))
else (if pc < 210 then
(if pc < 208 then
(if pc < 207 then
(if pc = 206 then some (.get 15) else none)
else (if pc = 207 then some (.const 4) else none))
else (if pc < 209 then
(if pc = 208 then some (.bin .lt) else none)
else (if pc = 209 then some (.brIf 0) else none)))
else (if pc < 212 then
(if pc < 211 then
(if pc = 210 then some (.get 15) else none)
else (if pc = 211 then some (.const 8) else none))
else (if pc < 213 then
(if pc = 212 then some (.bin .lt) else none)
else (if pc = 213 then some (.brIf 1) else none))))))
else (if pc < 229 then
(if pc < 221 then
(if pc < 217 then
(if pc < 215 then
(if pc = 214 then some (.get 15) else none)
else (if pc < 216 then
(if pc = 215 then some (.const 17) else none)
else (if pc = 216 then some (.bin .lt) else none)))
else (if pc < 219 then
(if pc < 218 then
(if pc = 217 then some (.brIf 2) else none)
else (if pc = 218 then some (.get 15) else none))
else (if pc < 220 then
(if pc = 219 then some (.const 33) else none)
else (if pc = 220 then some (.bin .lt) else none))))
else (if pc < 225 then
(if pc < 223 then
(if pc < 222 then
(if pc = 221 then some (.brIf 3) else none)
else (if pc = 222 then some (.get 15) else none))
else (if pc < 224 then
(if pc = 223 then some (.eqz) else none)
else (if pc = 224 then some (.brIf 13) else none)))
else (if pc < 227 then
(if pc < 226 then
(if pc = 225 then some (.get 11) else none)
else (if pc = 226 then some (.get 13) else none))
else (if pc < 228 then
(if pc = 227 then some (.get 15) else none)
else (if pc = 228 then some (.copy) else none)))))
else (if pc < 237 then
(if pc < 233 then
(if pc < 231 then
(if pc < 230 then
(if pc = 229 then some (.br 13) else none)
else (if pc = 230 then some (.end) else none))
else (if pc < 232 then
(if pc = 231 then some (.get 11) else none)
else (if pc = 232 then some (.get 13) else none)))
else (if pc < 235 then
(if pc < 234 then
(if pc = 233 then some (.load 1 0) else none)
else (if pc = 234 then some (.store 1 0) else none))
else (if pc < 236 then
(if pc = 235 then some (.get 15) else none)
else (if pc = 236 then some (.const 1) else none))))
else (if pc < 241 then
(if pc < 239 then
(if pc < 238 then
(if pc = 237 then some (.bin .eq) else none)
else (if pc = 238 then some (.brIf 12) else none))
else (if pc < 240 then
(if pc = 239 then some (.get 11) else none)
else (if pc = 240 then some (.get 13) else none)))
else (if pc < 243 then
(if pc < 242 then
(if pc = 241 then some (.load 2 0) else none)
else (if pc = 242 then some (.store 2 0) else none))
else (if pc < 244 then
(if pc = 243 then some (.get 11) else none)
else (if pc = 244 then some (.get 15) else none)))))))))
else (if pc < 368 then
(if pc < 306 then
(if pc < 275 then
(if pc < 260 then
(if pc < 252 then
(if pc < 248 then
(if pc < 246 then
(if pc = 245 then some (.const 4294967294) else none)
else (if pc < 247 then
(if pc = 246 then some (.bin .add) else none)
else (if pc = 247 then some (.tee 15) else none)))
else (if pc < 250 then
(if pc < 249 then
(if pc = 248 then some (.bin .add) else none)
else (if pc = 249 then some (.get 13) else none))
else (if pc < 251 then
(if pc = 250 then some (.get 15) else none)
else (if pc = 251 then some (.bin .add) else none))))
else (if pc < 256 then
(if pc < 254 then
(if pc < 253 then
(if pc = 252 then some (.load 2 0) else none)
else (if pc = 253 then some (.store 2 0) else none))
else (if pc < 255 then
(if pc = 254 then some (.br 12) else none)
else (if pc = 255 then some (.end) else none)))
else (if pc < 258 then
(if pc < 257 then
(if pc = 256 then some (.get 11) else none)
else (if pc = 257 then some (.get 13) else none))
else (if pc < 259 then
(if pc = 258 then some (.load 4 0) else none)
else (if pc = 259 then some (.store 4 0) else none)))))
else (if pc < 267 then
(if pc < 263 then
(if pc < 261 then
(if pc = 260 then some (.get 11) else none)
else (if pc < 262 then
(if pc = 261 then some (.get 15) else none)
else (if pc = 262 then some (.const 4294967292) else none)))
else (if pc < 265 then
(if pc < 264 then
(if pc = 263 then some (.bin .add) else none)
else (if pc = 264 then some (.tee 15) else none))
else (if pc < 266 then
(if pc = 265 then some (.bin .add) else none)
else (if pc = 266 then some (.get 13) else none))))
else (if pc < 271 then
(if pc < 269 then
(if pc < 268 then
(if pc = 267 then some (.get 15) else none)
else (if pc = 268 then some (.bin .add) else none))
else (if pc < 270 then
(if pc = 269 then some (.load 4 0) else none)
else (if pc = 270 then some (.store 4 0) else none)))
else (if pc < 273 then
(if pc < 272 then
(if pc = 271 then some (.br 11) else none)
else (if pc = 272 then some (.end) else none))
else (if pc < 274 then
(if pc = 273 then some (.get 11) else none)
else (if pc = 274 then some (.get 13) else none))))))
else (if pc < 290 then
(if pc < 282 then
(if pc < 278 then
(if pc < 276 then
(if pc = 275 then some (.load 8 0) else none)
else (if pc < 277 then
(if pc = 276 then some (.store 8 0) else none)
else (if pc = 277 then some (.get 11) else none)))
else (if pc < 280 then
(if pc < 279 then
(if pc = 278 then some (.get 15) else none)
else (if pc = 279 then some (.const 4294967288) else none))
else (if pc < 281 then
(if pc = 280 then some (.bin .add) else none)
else (if pc = 281 then some (.tee 15) else none))))
else (if pc < 286 then
(if pc < 284 then
(if pc < 283 then
(if pc = 282 then some (.bin .add) else none)
else (if pc = 283 then some (.get 13) else none))
else (if pc < 285 then
(if pc = 284 then some (.get 15) else none)
else (if pc = 285 then some (.bin .add) else none)))
else (if pc < 288 then
(if pc < 287 then
(if pc = 286 then some (.load 8 0) else none)
else (if pc = 287 then some (.store 8 0) else none))
else (if pc < 289 then
(if pc = 288 then some (.br 10) else none)
else (if pc = 289 then some (.end) else none)))))
else (if pc < 298 then
(if pc < 294 then
(if pc < 292 then
(if pc < 291 then
(if pc = 290 then some (.get 11) else none)
else (if pc = 291 then some (.get 13) else none))
else (if pc < 293 then
(if pc = 292 then some (.load 8 8) else none)
else (if pc = 293 then some (.store 8 8) else none)))
else (if pc < 296 then
(if pc < 295 then
(if pc = 294 then some (.get 11) else none)
else (if pc = 295 then some (.get 13) else none))
else (if pc < 297 then
(if pc = 296 then some (.load 8 0) else none)
else (if pc = 297 then some (.store 8 0) else none))))
else (if pc < 302 then
(if pc < 300 then
(if pc < 299 then
(if pc = 298 then some (.get 11) else none)
else (if pc = 299 then some (.get 15) else none))
else (if pc < 301 then
(if pc = 300 then some (.const 4294967280) else none)
else (if pc = 301 then some (.bin .add) else none)))
else (if pc < 304 then
(if pc < 303 then
(if pc = 302 then some (.tee 15) else none)
else (if pc = 303 then some (.bin .add) else none))
else (if pc < 305 then
(if pc = 304 then some (.tee 11) else none)
else (if pc = 305 then some (.get 13) else none)))))))
else (if pc < 337 then
(if pc < 321 then
(if pc < 313 then
(if pc < 309 then
(if pc < 307 then
(if pc = 306 then some (.get 15) else none)
else (if pc < 308 then
(if pc = 307 then some (.bin .add) else none)
else (if pc = 308 then some (.tee 15) else none)))
else (if pc < 311 then
(if pc < 310 then
(if pc = 309 then some (.load 8 8) else none)
else (if pc = 310 then some (.store 8 8) else none))
else (if pc < 312 then
(if pc = 311 then some (.get 11) else none)
else (if pc = 312 then some (.get 15) else none))))
else (if pc < 317 then
(if pc < 315 then
(if pc < 314 then
(if pc = 313 then some (.load 8 0) else none)
else (if pc = 314 then some (.store 8 0) else none))
else (if pc < 316 then
(if pc = 315 then some (.br 9) else none)
else (if pc = 316 then some (.end) else none)))
else (if pc < 319 then
(if pc < 318 then
(if pc = 317 then some (.get 10) else none)
else (if pc = 318 then some (.get 14) else none))
else (if pc < 320 then
(if pc = 319 then some (.get 3) else none)
else (if pc = 320 then some (.const 66164) else none)))))
else (if pc < 329 then
(if pc < 325 then
(if pc < 323 then
(if pc < 322 then
(if pc = 321 then some (.call 1) else none)
else (if pc = 322 then some (.trap) else none))
else (if pc < 324 then
(if pc = 323 then some (.end) else none)
else (if pc = 324 then some (.get 11) else none)))
else (if pc < 327 then
(if pc < 326 then
(if pc = 325 then some (.const 17) else none)
else (if pc = 326 then some (.bin .add) else none))
else (if pc < 328 then
(if pc = 327 then some (.tee 15) else none)
else (if pc = 328 then some (.get 2) else none))))
else (if pc < 333 then
(if pc < 331 then
(if pc < 330 then
(if pc = 329 then some (.bin .gt) else none)
else (if pc = 330 then some (.brIf 6) else none))
else (if pc < 332 then
(if pc = 331 then some (.get 10) else none)
else (if pc = 332 then some (.const 16) else none)))
else (if pc < 335 then
(if pc < 334 then
(if pc = 333 then some (.bin .add) else none)
else (if pc = 334 then some (.tee 15) else none))
else (if pc < 336 then
(if pc = 335 then some (.get 3) else none)
else (if pc = 336 then some (.bin .gt) else none))))))
else (if pc < 352 then
(if pc < 344 then
(if pc < 340 then
(if pc < 338 then
(if pc = 337 then some (.brIf 1) else none)
else (if pc < 339 then
(if pc = 338 then some (.get 1) else none)
else (if pc = 339 then some (.get 10) else none)))
else (if pc < 342 then
(if pc < 341 then
(if pc = 340 then some (.bin .add) else none)
else (if pc = 341 then some (.tee 15) else none))
else (if pc < 343 then
(if pc = 342 then some (.get 0) else none)
else (if pc = 343 then some (.get 4) else none))))
else (if pc < 348 then
(if pc < 346 then
(if pc < 345 then
(if pc = 344 then some (.bin .add) else none)
else (if pc = 345 then some (.tee 4) else none))
else (if pc < 347 then
(if pc = 346 then some (.load 8 0) else none)
else (if pc = 347 then some (.store 8 0) else none)))
else (if pc < 350 then
(if pc < 349 then
(if pc = 348 then some (.get 15) else none)
else (if pc = 349 then some (.get 4) else none))
else (if pc < 351 then
(if pc = 350 then some (.load 8 8) else none)
else (if pc = 351 then some (.store 8 8) else none)))))
else (if pc < 360 then
(if pc < 356 then
(if pc < 354 then
(if pc < 353 then
(if pc = 352 then some (.const 4294967295) else none)
else (if pc = 353 then some (.set 16) else none))
else (if pc < 355 then
(if pc = 354 then some (.get 4) else none)
else (if pc = 355 then some (.get 13) else none)))
else (if pc < 358 then
(if pc < 357 then
(if pc = 356 then some (.const 4) else none)
else (if pc = 357 then some (.bin .shr) else none))
else (if pc < 359 then
(if pc = 358 then some (.tee 17) else none)
else (if pc = 359 then some (.bin .add) else none))))
else (if pc < 364 then
(if pc < 362 then
(if pc < 361 then
(if pc = 360 then some (.load 2 0) else none)
else (if pc = 361 then some (.tee 18) else none))
else (if pc < 363 then
(if pc = 362 then some (.eqz) else none)
else (if pc = 363 then some (.brIf 9) else none)))
else (if pc < 366 then
(if pc < 365 then
(if pc = 364 then some (.get 10) else none)
else (if pc = 365 then some (.get 17) else none))
else (if pc < 367 then
(if pc = 366 then some (.bin .add) else none)
else (if pc = 367 then some (.tee 4) else none))))))))
else (if pc < 429 then
(if pc < 398 then
(if pc < 383 then
(if pc < 375 then
(if pc < 371 then
(if pc < 369 then
(if pc = 368 then some (.get 18) else none)
else (if pc < 370 then
(if pc = 369 then some (.bin .lt) else none)
else (if pc = 370 then some (.brIf 9) else none)))
else (if pc < 373 then
(if pc < 372 then
(if pc = 371 then some (.get 4) else none)
else (if pc = 372 then some (.get 18) else none))
else (if pc < 374 then
(if pc = 373 then some (.bin .sub) else none)
else (if pc = 374 then some (.set 15) else none))))
else (if pc < 379 then
(if pc < 377 then
(if pc < 376 then
(if pc = 375 then some (.block 499) else none)
else (if pc = 376 then some (.block 457) else none))
else (if pc < 378 then
(if pc = 377 then some (.get 18) else none)
else (if pc = 378 then some (.get 14) else none)))
else (if pc < 381 then
(if pc < 380 then
(if pc = 379 then some (.const 4) else none)
else (if pc = 380 then some (.bin .add) else none))
else (if pc < 382 then
(if pc = 381 then some (.tee 12) else none)
else (if pc = 382 then some (.bin .ge) else none)))))
else (if pc < 390 then
(if pc < 386 then
(if pc < 384 then
(if pc = 383 then some (.brIf 0) else none)
else (if pc < 385 then
(if pc = 384 then some (.get 4) else none)
else (if pc = 385 then some (.get 4) else none)))
else (if pc < 388 then
(if pc < 387 then
(if pc = 386 then some (.get 3) else none)
else (if pc = 387 then some (.get 4) else none))
else (if pc < 389 then
(if pc = 388 then some (.get 3) else none)
else (if pc = 389 then some (.bin .gt) else none))))
else (if pc < 394 then
(if pc < 392 then
(if pc < 391 then
(if pc = 390 then some (.select) else none)
else (if pc = 391 then some (.tee 19) else none))
else (if pc < 393 then
(if pc = 392 then some (.bin .sub) else none)
else (if pc = 393 then some (.set 14) else none)))
else (if pc < 396 then
(if pc < 395 then
(if pc = 394 then some (.get 13) else none)
else (if pc = 395 then some (.const 15) else none))
else (if pc < 397 then
(if pc = 396 then some (.bin .band) else none)
else (if pc = 397 then some (.set 13) else none))))))
else (if pc < 413 then
(if pc < 405 then
(if pc < 401 then
(if pc < 399 then
(if pc = 398 then some (.get 1) else none)
else (if pc < 400 then
(if pc = 399 then some (.get 4) else none)
else (if pc = 400 then some (.bin .add) else none)))
else (if pc < 403 then
(if pc < 402 then
(if pc = 401 then some (.set 18) else none)
else (if pc = 402 then some (.get 4) else none))
else (if pc < 404 then
(if pc = 403 then some (.get 12) else none)
else (if pc = 404 then some (.bin .add) else none))))
else (if pc < 409 then
(if pc < 407 then
(if pc < 406 then
(if pc = 405 then some (.set 10) else none)
else (if pc = 406 then some (.get 1) else none))
else (if pc < 408 then
(if pc = 407 then some (.get 15) else none)
else (if pc = 408 then some (.bin .add) else none)))
else (if pc < 411 then
(if pc < 410 then
(if pc = 409 then some (.set 12) else none)
else (if pc = 410 then some (.const 4294967292) else none))
else (if pc < 412 then
(if pc = 411 then some (.set 4) else none)
else (if pc = 412 then some (.loop 451) else none)))))
else (if pc < 421 then
(if pc < 417 then
(if pc < 415 then
(if pc < 414 then
(if pc = 413 then some (.get 15) else none)
else (if pc = 414 then some (.get 4) else none))
else (if pc < 416 then
(if pc = 415 then some (.bin .add) else none)
else (if pc = 416 then some (.const 4) else none)))
else (if pc < 419 then
(if pc < 418 then
(if pc = 417 then some (.bin .add) else none)
else (if pc = 418 then some (.tee 20) else none))
else (if pc < 420 then
(if pc = 419 then some (.get 3) else none)
else (if pc = 420 then some (.bin .ge) else none))))
else (if pc < 425 then
(if pc < 423 then
(if pc < 422 then
(if pc = 421 then some (.brIf 5) else none)
else (if pc = 422 then some (.block 450) else none))
else (if pc < 424 then
(if pc = 423 then some (.get 14) else none)
else (if pc = 424 then some (.get 4) else none)))
else (if pc < 427 then
(if pc < 426 then
(if pc = 425 then some (.bin .add) else none)
else (if pc = 426 then some (.const 4294967292) else none))
else (if pc < 428 then
(if pc = 427 then some (.bin .eq) else none)
else (if pc = 428 then some (.brIf 0) else none)))))))
else (if pc < 460 then
(if pc < 444 then
(if pc < 436 then
(if pc < 432 then
(if pc < 430 then
(if pc = 429 then some (.get 18) else none)
else (if pc < 431 then
(if pc = 430 then some (.get 4) else none)
else (if pc = 431 then some (.bin .add) else none)))
else (if pc < 434 then
(if pc < 433 then
(if pc = 432 then some (.const 4) else none)
else (if pc = 433 then some (.bin .add) else none))
else (if pc < 435 then
(if pc = 434 then some (.get 12) else none)
else (if pc = 435 then some (.get 4) else none))))
else (if pc < 440 then
(if pc < 438 then
(if pc < 437 then
(if pc = 436 then some (.bin .add) else none)
else (if pc = 437 then some (.const 4) else none))
else (if pc < 439 then
(if pc = 438 then some (.bin .add) else none)
else (if pc = 439 then some (.load 1 0) else none)))
else (if pc < 442 then
(if pc < 441 then
(if pc = 440 then some (.store 1 0) else none)
else (if pc = 441 then some (.get 13) else none))
else (if pc < 443 then
(if pc = 442 then some (.get 4) else none)
else (if pc = 443 then some (.const 1) else none)))))
else (if pc < 452 then
(if pc < 448 then
(if pc < 446 then
(if pc < 445 then
(if pc = 444 then some (.bin .add) else none)
else (if pc = 445 then some (.tee 4) else none))
else (if pc < 447 then
(if pc = 446 then some (.bin .ne) else none)
else (if pc = 447 then some (.brIf 1) else none)))
else (if pc < 450 then
(if pc < 449 then
(if pc = 448 then some (.br 3) else none)
else (if pc = 449 then some (.end) else none))
else (if pc < 451 then
(if pc = 450 then some (.end) else none)
else (if pc = 451 then some (.get 19) else none))))
else (if pc < 456 then
(if pc < 454 then
(if pc < 453 then
(if pc = 452 then some (.get 3) else none)
else (if pc = 453 then some (.const 66196) else none))
else (if pc < 455 then
(if pc = 454 then some (.call 2) else none)
else (if pc = 455 then some (.trap) else none)))
else (if pc < 458 then
(if pc < 457 then
(if pc = 456 then some (.end) else none)
else (if pc = 457 then some (.get 15) else none))
else (if pc < 459 then
(if pc = 458 then some (.const 18) else none)
else (if pc = 459 then some (.bin .add) else none))))))
else (if pc < 475 then
(if pc < 467 then
(if pc < 463 then
(if pc < 461 then
(if pc = 460 then some (.tee 14) else none)
else (if pc < 462 then
(if pc = 461 then some (.get 3) else none)
else (if pc = 462 then some (.bin .gt) else none)))
else (if pc < 465 then
(if pc < 464 then
(if pc = 463 then some (.brIf 4) else none)
else (if pc = 464 then some (.get 15) else none))
else (if pc < 466 then
(if pc = 465 then some (.const 4294967278) else none)
else (if pc = 466 then some (.bin .ge) else none))))
else (if pc < 471 then
(if pc < 469 then
(if pc < 468 then
(if pc = 467 then some (.brIf 5) else none)
else (if pc = 468 then some (.get 4) else none))
else (if pc < 470 then
(if pc = 469 then some (.get 9) else none)
else (if pc = 470 then some (.bin .gt) else none)))
else (if pc < 473 then
(if pc < 472 then
(if pc = 471 then some (.brIf 6) else none)
else (if pc = 472 then some (.get 1) else none))
else (if pc < 474 then
(if pc = 473 then some (.get 15) else none)
else (if pc = 474 then some (.bin .add) else none)))))
else (if pc < 483 then
(if pc < 479 then
(if pc < 477 then
(if pc < 476 then
(if pc = 475 then some (.tee 15) else none)
else (if pc = 476 then some (.load 8 0) else none))
else (if pc < 478 then
(if pc = 477 then some (.set 21) else none)
else (if pc = 478 then some (.get 15) else none)))
else (if pc < 481 then
(if pc < 480 then
(if pc = 479 then some (.load 8 8) else none)
else (if pc = 480 then some (.set 22) else none))
else (if pc < 482 then
(if pc = 481 then some (.get 1) else none)
else (if pc = 482 then some (.get 4) else none))))
else (if pc < 487 then
(if pc < 485 then
(if pc < 484 then
(if pc = 483 then some (.bin .add) else none)
else (if pc = 484 then some (.tee 14) else none))
else (if pc < 486 then
(if pc = 485 then some (.get 15) else none)
else (if pc = 486 then some (.load 2 16) else none)))
else (if pc < 489 then
(if pc < 488 then
(if pc = 487 then some (.store 2 16) else none)
else (if pc = 488 then some (.get 14) else none))
else (if pc < 490 then
(if pc = 489 then some (.get 22) else none)
else (if pc = 490 then some (.store 8 8) else none))))))))))
else (if pc < 736 then
(if pc < 613 then
(if pc < 552 then
(if pc < 521 then
(if pc < 506 then
(if pc < 498 then
(if pc < 494 then
(if pc < 492 then
(if pc = 491 then some (.get 14) else none)
else (if pc < 493 then
(if pc = 492 then some (.get 21) else none)
else (if pc = 493 then some (.store 8 0) else none)))
else (if pc < 496 then
(if pc < 495 then
(if pc = 494 then some (.get 4) else none)
else (if pc = 495 then some (.get 12) else none))
else (if pc < 497 then
(if pc = 496 then some (.bin .add) else none)
else (if pc = 497 then some (.set 10) else none))))
else (if pc < 502 then
(if pc < 500 then
(if pc < 499 then
(if pc = 498 then some (.end) else none)
else (if pc = 499 then some (.get 11) else none))
else (if pc < 501 then
(if pc = 500 then some (.get 17) else none)
else (if pc = 501 then some (.bin .add) else none)))
else (if pc < 504 then
(if pc < 503 then
(if pc = 502 then some (.const 3) else none)
else (if pc = 503 then some (.bin .add) else none))
else (if pc < 505 then
(if pc = 504 then some (.tee 11) else none)
else (if pc = 505 then some (.get 2) else none)))))
else (if pc < 513 then
(if pc < 509 then
(if pc < 507 then
(if pc = 506 then some (.bin .lt) else none)
else (if pc < 508 then
(if pc = 507 then some (.brIf 8) else none)
else (if pc = 508 then some (.br 9) else none)))
else (if pc < 511 then
(if pc < 510 then
(if pc = 509 then some (.end) else none)
else (if pc = 510 then some (.get 13) else none))
else (if pc < 512 then
(if pc = 511 then some (.get 4) else none)
else (if pc = 512 then some (.get 2) else none))))
else (if pc < 517 then
(if pc < 515 then
(if pc < 514 then
(if pc = 513 then some (.const 65956) else none)
else (if pc = 514 then some (.call 1) else none))
else (if pc < 516 then
(if pc = 515 then some (.trap) else none)
else (if pc = 516 then some (.end) else none)))
else (if pc < 519 then
(if pc < 518 then
(if pc = 517 then some (.get 10) else none)
else (if pc = 518 then some (.get 15) else none))
else (if pc < 520 then
(if pc = 519 then some (.get 3) else none)
else (if pc = 520 then some (.const 66164) else none))))))
else (if pc < 536 then
(if pc < 528 then
(if pc < 524 then
(if pc < 522 then
(if pc = 521 then some (.call 1) else none)
else (if pc < 523 then
(if pc = 522 then some (.trap) else none)
else (if pc = 523 then some (.end) else none)))
else (if pc < 526 then
(if pc < 525 then
(if pc = 524 then some (.get 20) else none)
else (if pc = 525 then some (.get 3) else none))
else (if pc < 527 then
(if pc = 526 then some (.const 66180) else none)
else (if pc = 527 then some (.call 2) else none))))
else (if pc < 532 then
(if pc < 530 then
(if pc < 529 then
(if pc = 528 then some (.trap) else none)
else (if pc = 529 then some (.end) else none))
else (if pc < 531 then
(if pc = 530 then some (.const 0) else none)
else (if pc = 531 then some (.get 14) else none)))
else (if pc < 534 then
(if pc < 533 then
(if pc = 532 then some (.get 3) else none)
else (if pc = 533 then some (.const 66020) else none))
else (if pc < 535 then
(if pc = 534 then some (.call 1) else none)
else (if pc = 535 then some (.trap) else none)))))
else (if pc < 544 then
(if pc < 540 then
(if pc < 538 then
(if pc < 537 then
(if pc = 536 then some (.end) else none)
else (if pc = 537 then some (.get 15) else none))
else (if pc < 539 then
(if pc = 538 then some (.get 14) else none)
else (if pc = 539 then some (.get 3) else none)))
else (if pc < 542 then
(if pc < 541 then
(if pc = 540 then some (.const 66036) else none)
else (if pc = 541 then some (.call 1) else none))
else (if pc < 543 then
(if pc = 542 then some (.trap) else none)
else (if pc = 543 then some (.end) else none))))
else (if pc < 548 then
(if pc < 546 then
(if pc < 545 then
(if pc = 544 then some (.const 65536) else none)
else (if pc = 545 then some (.const 43) else none))
else (if pc < 547 then
(if pc = 546 then some (.const 66148) else none)
else (if pc = 547 then some (.call 8) else none)))
else (if pc < 550 then
(if pc < 549 then
(if pc = 548 then some (.trap) else none)
else (if pc = 549 then some (.end) else none))
else (if pc < 551 then
(if pc = 550 then some (.get 4) else none)
else (if pc = 551 then some (.get 15) else none)))))))
else (if pc < 582 then
(if pc < 567 then
(if pc < 559 then
(if pc < 555 then
(if pc < 553 then
(if pc = 552 then some (.get 2) else none)
else (if pc < 554 then
(if pc = 553 then some (.const 65972) else none)
else (if pc = 554 then some (.call 1) else none)))
else (if pc < 557 then
(if pc < 556 then
(if pc = 555 then some (.trap) else none)
else (if pc = 556 then some (.end) else none))
else (if pc < 558 then
(if pc = 557 then some (.block 565) else none)
else (if pc = 558 then some (.get 4) else none))))
else (if pc < 563 then
(if pc < 561 then
(if pc < 560 then
(if pc = 559 then some (.get 2) else none)
else (if pc = 560 then some (.bin .lt) else none))
else (if pc < 562 then
(if pc = 561 then some (.brIf 0) else none)
else (if pc = 562 then some (.get 14) else none)))
else (if pc < 565 then
(if pc < 564 then
(if pc = 563 then some (.ret) else none)
else (if pc = 564 then some (.end) else none))
else (if pc < 566 then
(if pc = 565 then some (.const 4294967295) else none)
else (if pc = 566 then some (.set 16) else none)))))
else (if pc < 574 then
(if pc < 570 then
(if pc < 568 then
(if pc = 567 then some (.get 4) else none)
else (if pc < 569 then
(if pc = 568 then some (.const 2) else none)
else (if pc = 569 then some (.bin .add) else none)))
else (if pc < 572 then
(if pc < 571 then
(if pc = 570 then some (.tee 15) else none)
else (if pc = 571 then some (.get 2) else none))
else (if pc < 573 then
(if pc = 572 then some (.bin .gt) else none)
else (if pc = 573 then some (.brIf 1) else none))))
else (if pc < 578 then
(if pc < 576 then
(if pc < 575 then
(if pc = 574 then some (.get 0) else none)
else (if pc = 575 then some (.get 4) else none))
else (if pc < 577 then
(if pc = 576 then some (.bin .add) else none)
else (if pc = 577 then some (.load 2 0) else none)))
else (if pc < 580 then
(if pc < 579 then
(if pc = 578 then some (.tee 18) else none)
else (if pc = 579 then some (.eqz) else none))
else (if pc < 581 then
(if pc = 580 then some (.brIf 1) else none)
else (if pc = 581 then some (.block 624) else none))))))
else (if pc < 597 then
(if pc < 589 then
(if pc < 585 then
(if pc < 583 then
(if pc = 582 then some (.block 594) else none)
else (if pc < 584 then
(if pc = 583 then some (.get 12) else none)
else (if pc = 584 then some (.const 4) else none)))
else (if pc < 587 then
(if pc < 586 then
(if pc = 585 then some (.bin .add) else none)
else (if pc = 586 then some (.tee 4) else none))
else (if pc < 588 then
(if pc = 587 then some (.const 19) else none)
else (if pc = 588 then some (.bin .eq) else none))))
else (if pc < 593 then
(if pc < 591 then
(if pc < 590 then
(if pc = 589 then some (.brIf 0) else none)
else (if pc = 590 then some (.get 15) else none))
else (if pc < 592 then
(if pc = 591 then some (.set 11) else none)
else (if pc = 592 then some (.br 1) else none)))
else (if pc < 595 then
(if pc < 594 then
(if pc = 593 then some (.end) else none)
else (if pc = 594 then some (.const 0) else none))
else (if pc < 596 then
(if pc = 595 then some (.set 4) else none)
else (if pc = 596 then some (.loop 619) else none)))))
else (if pc < 605 then
(if pc < 601 then
(if pc < 599 then
(if pc < 598 then
(if pc = 597 then some (.get 2) else none)
else (if pc = 598 then some (.get 15) else none))
else (if pc < 600 then
(if pc = 599 then some (.bin .eq) else none)
else (if pc = 600 then some (.brIf 3) else none)))
else (if pc < 603 then
(if pc < 602 then
(if pc = 601 then some (.get 4) else none)
else (if pc = 602 then some (.get 0) else none))
else (if pc < 604 then
(if pc = 603 then some (.get 15) else none)
else (if pc = 604 then some (.bin .add) else none))))
else (if pc < 609 then
(if pc < 607 then
(if pc < 606 then
(if pc = 605 then some (.load 1 0) else none)
else (if pc = 606 then some (.tee 13) else none))
else (if pc < 608 then
(if pc = 607 then some (.bin .add) else none)
else (if pc = 608 then some (.set 4) else none)))
else (if pc < 611 then
(if pc < 610 then
(if pc = 609 then some (.get 15) else none)
else (if pc = 610 then some (.const 1) else none))
else (if pc < 612 then
(if pc = 611 then some (.bin .add) else none)
else (if pc = 612 then some (.tee 11) else none))))))))
else (if pc < 674 then
(if pc < 643 then
(if pc < 628 then
(if pc < 620 then
(if pc < 616 then
(if pc < 614 then
(if pc = 613 then some (.set 15) else none)
else (if pc < 615 then
(if pc = 614 then some (.get 13) else none)
else (if pc = 615 then some (.const 255) else none)))
else (if pc < 618 then
(if pc < 617 then
(if pc = 616 then some (.bin .eq) else none)
else (if pc = 617 then some (.brIf 0) else none))
else (if pc < 619 then
(if pc = 618 then some (.end) else none)
else (if pc = 619 then some (.get 4) else none))))
else (if pc < 624 then
(if pc < 622 then
(if pc < 621 then
(if pc = 620 then some (.const 19) else none)
else (if pc = 621 then some (.bin .add) else none))
else (if pc < 623 then
(if pc = 622 then some (.set 4) else none)
else (if pc = 623 then some (.end) else none)))
else (if pc < 626 then
(if pc < 625 then
(if pc = 624 then some (.get 4) else none)
else (if pc = 625 then some (.get 14) else none))
else (if pc < 627 then
(if pc = 626 then some (.bin .add) else none)
else (if pc = 627 then some (.tee 10) else none)))))
else (if pc < 635 then
(if pc < 631 then
(if pc < 629 then
(if pc = 628 then some (.get 3) else none)
else (if pc < 630 then
(if pc = 629 then some (.bin .gt) else none)
else (if pc = 630 then some (.brIf 1) else none)))
else (if pc < 633 then
(if pc < 632 then
(if pc = 631 then some (.get 14) else none)
else (if pc = 632 then some (.get 18) else none))
else (if pc < 634 then
(if pc = 633 then some (.bin .sub) else none)
else (if pc = 634 then some (.set 15) else none))))
else (if pc < 639 then
(if pc < 637 then
(if pc < 636 then
(if pc = 635 then some (.block 894) else none)
else (if pc = 636 then some (.block 850) else none))
else (if pc < 638 then
(if pc = 637 then some (.block 820) else none)
else (if pc = 638 then some (.block 813) else none)))
else (if pc < 641 then
(if pc < 640 then
(if pc = 639 then some (.block 731) else none)
else (if pc = 640 then some (.get 4) else none))
else (if pc < 642 then
(if pc = 641 then some (.get 18) else none)
else (if pc = 642 then some (.bin .gt) else none))))))
else (if pc < 658 then
(if pc < 650 then
(if pc < 646 then
(if pc < 644 then
(if pc = 643 then some (.brIf 0) else none)
else (if pc < 645 then
(if pc = 644 then some (.get 14) else none)
else (if pc = 645 then some (.get 18) else none)))
else (if pc < 648 then
(if pc < 647 then
(if pc = 646 then some (.bin .lt) else none)
else (if pc = 647 then some (.brIf 6) else none))
else (if pc < 649 then
(if pc = 648 then some (.get 4) else none)
else (if pc = 649 then some (.const 33) else none))))
else (if pc < 654 then
(if pc < 652 then
(if pc < 651 then
(if pc = 650 then some (.bin .lt) else none)
else (if pc = 651 then some (.brIf 1) else none))
else (if pc < 653 then
(if pc = 652 then some (.get 14) else none)
else (if pc = 653 then some (.const 64) else none)))
else (if pc < 656 then
(if pc < 655 then
(if pc = 654 then some (.bin .add) else none)
else (if pc = 655 then some (.get 3) else none))
else (if pc < 657 then
(if pc = 656 then some (.bin .gt) else none)
else (if pc = 657 then some (.brIf 2) else none)))))
else (if pc < 666 then
(if pc < 662 then
(if pc < 660 then
(if pc < 659 then
(if pc = 658 then some (.get 4) else none)
else (if pc = 659 then some (.const 64) else none))
else (if pc < 661 then
(if pc = 660 then some (.bin .gt) else none)
else (if pc = 661 then some (.brIf 2) else none)))
else (if pc < 664 then
(if pc < 663 then
(if pc = 662 then some (.get 15) else none)
else (if pc = 663 then some (.const 64) else none))
else (if pc < 665 then
(if pc = 664 then some (.bin .add) else none)
else (if pc = 665 then some (.tee 4) else none))))
else (if pc < 670 then
(if pc < 668 then
(if pc < 667 then
(if pc = 666 then some (.get 3) else none)
else (if pc = 667 then some (.bin .gt) else none))
else (if pc < 669 then
(if pc = 668 then some (.brIf 13) else none)
else (if pc = 669 then some (.get 15) else none)))
else (if pc < 672 then
(if pc < 671 then
(if pc = 670 then some (.const 4294967232) else none)
else (if pc = 671 then some (.bin .ge) else none))
else (if pc < 673 then
(if pc = 672 then some (.brIf 14) else none)
else (if pc = 673 then some (.get 14) else none)))))))
else (if pc < 705 then
(if pc < 689 then
(if pc < 681 then
(if pc < 677 then
(if pc < 675 then
(if pc = 674 then some (.get 8) else none)
else (if pc < 676 then
(if pc = 675 then some (.bin .gt) else none)
else (if pc = 676 then some (.brIf 15) else none)))
else (if pc < 679 then
(if pc < 678 then
(if pc = 677 then some (.get 1) else none)
else (if pc = 678 then some (.get 15) else none))
else (if pc < 680 then
(if pc = 679 then some (.bin .add) else none)
else (if pc = 680 then some (.tee 4) else none))))
else (if pc < 685 then
(if pc < 683 then
(if pc < 682 then
(if pc = 681 then some (.load 8 0) else none)
else (if pc = 682 then some (.set 21) else none))
else (if pc < 684 then
(if pc = 683 then some (.get 4) else none)
else (if pc = 684 then some (.load 8 8) else none)))
else (if pc < 687 then
(if pc < 686 then
(if pc = 685 then some (.set 22) else none)
else (if pc = 686 then some (.get 4) else none))
else (if pc < 688 then
(if pc = 687 then some (.load 8 16) else none)
else (if pc = 688 then some (.set 23) else none)))))
else (if pc < 697 then
(if pc < 693 then
(if pc < 691 then
(if pc < 690 then
(if pc = 689 then some (.get 4) else none)
else (if pc = 690 then some (.load 8 24) else none))
else (if pc < 692 then
(if pc = 691 then some (.set 24) else none)
else (if pc = 692 then some (.get 4) else none)))
else (if pc < 695 then
(if pc < 694 then
(if pc = 693 then some (.load 8 32) else none)
else (if pc = 694 then some (.set 25) else none))
else (if pc < 696 then
(if pc = 695 then some (.get 4) else none)
else (if pc = 696 then some (.load 8 40) else none))))
else (if pc < 701 then
(if pc < 699 then
(if pc < 698 then
(if pc = 697 then some (.set 26) else none)
else (if pc = 698 then some (.get 4) else none))
else (if pc < 700 then
(if pc = 699 then some (.load 8 48) else none)
else (if pc = 700 then some (.set 27) else none)))
else (if pc < 703 then
(if pc < 702 then
(if pc = 701 then some (.get 1) else none)
else (if pc = 702 then some (.get 14) else none))
else (if pc < 704 then
(if pc = 703 then some (.bin .add) else none)
else (if pc = 704 then some (.tee 15) else none))))))
else (if pc < 720 then
(if pc < 712 then
(if pc < 708 then
(if pc < 706 then
(if pc = 705 then some (.get 4) else none)
else (if pc < 707 then
(if pc = 706 then some (.load 8 56) else none)
else (if pc = 707 then some (.store 8 56) else none)))
else (if pc < 710 then
(if pc < 709 then
(if pc = 708 then some (.get 15) else none)
else (if pc = 709 then some (.get 27) else none))
else (if pc < 711 then
(if pc = 710 then some (.store 8 48) else none)
else (if pc = 711 then some (.get 15) else none))))
else (if pc < 716 then
(if pc < 714 then
(if pc < 713 then
(if pc = 712 then some (.get 26) else none)
else (if pc = 713 then some (.store 8 40) else none))
else (if pc < 715 then
(if pc = 714 then some (.get 15) else none)
else (if pc = 715 then some (.get 25) else none)))
else (if pc < 718 then
(if pc < 717 then
(if pc = 716 then some (.store 8 32) else none)
else (if pc = 717 then some (.get 15) else none))
else (if pc < 719 then
(if pc = 718 then some (.get 24) else none)
else (if pc = 719 then some (.store 8 24) else none)))))
else (if pc < 728 then
(if pc < 724 then
(if pc < 722 then
(if pc < 721 then
(if pc = 720 then some (.get 15) else none)
else (if pc = 721 then some (.get 23) else none))
else (if pc < 723 then
(if pc = 722 then some (.store 8 16) else none)
else (if pc = 723 then some (.get 15) else none)))
else (if pc < 726 then
(if pc < 725 then
(if pc = 724 then some (.get 22) else none)
else (if pc = 725 then some (.store 8 8) else none))
else (if pc < 727 then
(if pc = 726 then some (.get 15) else none)
else (if pc = 727 then some (.get 21) else none))))
else (if pc < 732 then
(if pc < 730 then
(if pc < 729 then
(if pc = 728 then some (.store 8 0) else none)
else (if pc = 729 then some (.br 4) else none))
else (if pc < 731 then
(if pc = 730 then some (.end) else none)
else (if pc = 731 then some (.get 14) else none)))
else (if pc < 734 then
(if pc < 733 then
(if pc = 732 then some (.get 18) else none)
else (if pc = 733 then some (.bin .lt) else none))
else (if pc < 735 then
(if pc = 734 then some (.brIf 5) else none)
else (if pc = 735 then some (.block 762) else none)))))))))
else (if pc < 859 then
(if pc < 797 then
(if pc < 766 then
(if pc < 751 then
(if pc < 743 then
(if pc < 739 then
(if pc < 737 then
(if pc = 736 then some (.get 18) else none)
else (if pc < 738 then
(if pc = 737 then some (.const 1) else none)
else (if pc = 738 then some (.bin .ne) else none)))
else (if pc < 741 then
(if pc < 740 then
(if pc = 739 then some (.brIf 0) else none)
else (if pc = 740 then some (.get 15) else none))
else (if pc < 742 then
(if pc = 741 then some (.get 3) else none)
else (if pc = 742 then some (.bin .ge) else none))))
else (if pc < 747 then
(if pc < 745 then
(if pc < 744 then
(if pc = 743 then some (.brIf 7) else none)
else (if pc = 744 then some (.get 10) else none))
else (if pc < 746 then
(if pc = 745 then some (.get 14) else none)
else (if pc = 746 then some (.bin .lt) else none)))
else (if pc < 749 then
(if pc < 748 then
(if pc = 747 then some (.brIf 8) else none)
else (if pc = 748 then some (.get 4) else none))
else (if pc < 750 then
(if pc = 749 then some (.eqz) else none)
else (if pc = 750 then some (.brIf 4) else none)))))
else (if pc < 758 then
(if pc < 754 then
(if pc < 752 then
(if pc = 751 then some (.get 1) else none)
else (if pc < 753 then
(if pc = 752 then some (.get 14) else none)
else (if pc = 753 then some (.bin .add) else none)))
else (if pc < 756 then
(if pc < 755 then
(if pc = 754 then some (.get 1) else none)
else (if pc = 755 then some (.get 15) else none))
else (if pc < 757 then
(if pc = 756 then some (.bin .add) else none)
else (if pc = 757 then some (.load 1 0) else none))))
else (if pc < 762 then
(if pc < 760 then
(if pc < 759 then
(if pc = 758 then some (.get 4) else none)
else (if pc = 759 then some (.fill) else none))
else (if pc < 761 then
(if pc = 760 then some (.br 4) else none)
else (if pc = 761 then some (.end) else none)))
else (if pc < 764 then
(if pc < 763 then
(if pc = 762 then some (.get 14) else none)
else (if pc = 763 then some (.get 10) else none))
else (if pc < 765 then
(if pc = 764 then some (.bin .ge) else none)
else (if pc = 765 then some (.brIf 3) else none))))))
else (if pc < 781 then
(if pc < 773 then
(if pc < 769 then
(if pc < 767 then
(if pc = 766 then some (.get 1) else none)
else (if pc < 768 then
(if pc = 767 then some (.get 18) else none)
else (if pc = 768 then some (.bin .sub) else none)))
else (if pc < 771 then
(if pc < 770 then
(if pc = 769 then some (.set 13) else none)
else (if pc = 770 then some (.const 0) else none))
else (if pc < 772 then
(if pc = 771 then some (.get 18) else none)
else (if pc = 772 then some (.bin .sub) else none))))
else (if pc < 777 then
(if pc < 775 then
(if pc < 774 then
(if pc = 773 then some (.set 15) else none)
else (if pc = 774 then some (.loop 807) else none))
else (if pc < 776 then
(if pc = 775 then some (.get 15) else none)
else (if pc = 776 then some (.get 14) else none)))
else (if pc < 779 then
(if pc < 778 then
(if pc = 777 then some (.bin .add) else none)
else (if pc = 778 then some (.tee 18) else none))
else (if pc < 780 then
(if pc = 779 then some (.get 3) else none)
else (if pc = 780 then some (.bin .ge) else none)))))
else (if pc < 789 then
(if pc < 785 then
(if pc < 783 then
(if pc < 782 then
(if pc = 781 then some (.brIf 9) else none)
else (if pc = 782 then some (.block 806) else none))
else (if pc < 784 then
(if pc = 783 then some (.get 3) else none)
else (if pc = 784 then some (.get 14) else none)))
else (if pc < 787 then
(if pc < 786 then
(if pc = 785 then some (.bin .eq) else none)
else (if pc = 786 then some (.brIf 0) else none))
else (if pc < 788 then
(if pc = 787 then some (.get 1) else none)
else (if pc = 788 then some (.get 14) else none))))
else (if pc < 793 then
(if pc < 791 then
(if pc < 790 then
(if pc = 789 then some (.bin .add) else none)
else (if pc = 790 then some (.get 13) else none))
else (if pc < 792 then
(if pc = 791 then some (.get 14) else none)
else (if pc = 792 then some (.bin .add) else none)))
else (if pc < 795 then
(if pc < 794 then
(if pc = 793 then some (.load 1 0) else none)
else (if pc = 794 then some (.store 1 0) else none))
else (if pc < 796 then
(if pc = 795 then some (.get 14) else none)
else (if pc = 796 then some (.const 1) else none)))))))
else (if pc < 828 then
(if pc < 812 then
(if pc < 804 then
(if pc < 800 then
(if pc < 798 then
(if pc = 797 then some (.bin .add) else none)
else (if pc < 799 then
(if pc = 798 then some (.set 14) else none)
else (if pc = 799 then some (.get 4) else none)))
else (if pc < 802 then
(if pc < 801 then
(if pc = 800 then some (.const 4294967295) else none)
else (if pc = 801 then some (.bin .add) else none))
else (if pc < 803 then
(if pc = 802 then some (.tee 4) else none)
else (if pc = 803 then some (.brIf 1) else none))))
else (if pc < 808 then
(if pc < 806 then
(if pc < 805 then
(if pc = 804 then some (.br 5) else none)
else (if pc = 805 then some (.end) else none))
else (if pc < 807 then
(if pc = 806 then some (.end) else none)
else (if pc = 807 then some (.get 3) else none)))
else (if pc < 810 then
(if pc < 809 then
(if pc = 808 then some (.get 3) else none)
else (if pc = 809 then some (.const 66196) else none))
else (if pc < 811 then
(if pc = 810 then some (.call 2) else none)
else (if pc = 811 then some (.trap) else none)))))
else (if pc < 820 then
(if pc < 816 then
(if pc < 814 then
(if pc < 813 then
(if pc = 812 then some (.end) else none)
else (if pc = 813 then some (.get 14) else none))
else (if pc < 815 then
(if pc = 814 then some (.const 32) else none)
else (if pc = 815 then some (.bin .add) else none)))
else (if pc < 818 then
(if pc < 817 then
(if pc = 816 then some (.get 3) else none)
else (if pc = 817 then some (.bin .le) else none))
else (if pc < 819 then
(if pc = 818 then some (.brIf 1) else none)
else (if pc = 819 then some (.end) else none))))
else (if pc < 824 then
(if pc < 822 then
(if pc < 821 then
(if pc = 820 then some (.get 4) else none)
else (if pc = 821 then some (.get 15) else none))
else (if pc < 823 then
(if pc = 822 then some (.bin .add) else none)
else (if pc = 823 then some (.tee 13) else none)))
else (if pc < 826 then
(if pc < 825 then
(if pc = 824 then some (.get 3) else none)
else (if pc = 825 then some (.bin .gt) else none))
else (if pc < 827 then
(if pc = 826 then some (.brIf 7) else none)
else (if pc = 827 then some (.get 15) else none))))))
else (if pc < 843 then
(if pc < 835 then
(if pc < 831 then
(if pc < 829 then
(if pc = 828 then some (.get 13) else none)
else (if pc < 830 then
(if pc = 829 then some (.bin .gt) else none)
else (if pc = 830 then some (.brIf 8) else none)))
else (if pc < 833 then
(if pc < 832 then
(if pc = 831 then some (.get 14) else none)
else (if pc = 832 then some (.get 3) else none))
else (if pc < 834 then
(if pc = 833 then some (.get 4) else none)
else (if pc = 834 then some (.bin .sub) else none))))
else (if pc < 839 then
(if pc < 837 then
(if pc < 836 then
(if pc = 835 then some (.bin .gt) else none)
else (if pc = 836 then some (.brIf 9) else none))
else (if pc < 838 then
(if pc = 837 then some (.get 4) else none)
else (if pc = 838 then some (.eqz) else none)))
else (if pc < 841 then
(if pc < 840 then
(if pc = 839 then some (.brIf 1) else none)
else (if pc = 840 then some (.get 1) else none))
else (if pc < 842 then
(if pc = 841 then some (.get 14) else none)
else (if pc = 842 then some (.bin .add) else none)))))
else (if pc < 851 then
(if pc < 847 then
(if pc < 845 then
(if pc < 844 then
(if pc = 843 then some (.get 1) else none)
else (if pc = 844 then some (.get 15) else none))
else (if pc < 846 then
(if pc = 845 then some (.bin .add) else none)
else (if pc = 846 then some (.get 4) else none)))
else (if pc < 849 then
(if pc < 848 then
(if pc = 847 then some (.copy) else none)
else (if pc = 848 then some (.br 1) else none))
else (if pc < 850 then
(if pc = 849 then some (.end) else none)
else (if pc = 850 then some (.get 15) else none))))
else (if pc < 855 then
(if pc < 853 then
(if pc < 852 then
(if pc = 851 then some (.const 32) else none)
else (if pc = 852 then some (.bin .add) else none))
else (if pc < 854 then
(if pc = 853 then some (.tee 4) else none)
else (if pc = 854 then some (.get 3) else none)))
else (if pc < 857 then
(if pc < 856 then
(if pc = 855 then some (.bin .gt) else none)
else (if pc = 856 then some (.brIf 12) else none))
else (if pc < 858 then
(if pc = 857 then some (.get 15) else none)
else (if pc = 858 then some (.const 4294967264) else none))))))))
else (if pc < 920 then
(if pc < 889 then
(if pc < 874 then
(if pc < 866 then
(if pc < 862 then
(if pc < 860 then
(if pc = 859 then some (.bin .ge) else none)
else (if pc < 861 then
(if pc = 860 then some (.brIf 13) else none)
else (if pc = 861 then some (.get 14) else none)))
else (if pc < 864 then
(if pc < 863 then
(if pc = 862 then some (.get 7) else none)
else (if pc = 863 then some (.bin .gt) else none))
else (if pc < 865 then
(if pc = 864 then some (.brIf 14) else none)
else (if pc = 865 then some (.get 1) else none))))
else (if pc < 870 then
(if pc < 868 then
(if pc < 867 then
(if pc = 866 then some (.get 15) else none)
else (if pc = 867 then some (.bin .add) else none))
else (if pc < 869 then
(if pc = 868 then some (.tee 4) else none)
else (if pc = 869 then some (.load 8 0) else none)))
else (if pc < 872 then
(if pc < 871 then
(if pc = 870 then some (.set 21) else none)
else (if pc = 871 then some (.get 4) else none))
else (if pc < 873 then
(if pc = 872 then some (.load 8 8) else none)
else (if pc = 873 then some (.set 22) else none)))))
else (if pc < 881 then
(if pc < 877 then
(if pc < 875 then
(if pc = 874 then some (.get 4) else none)
else (if pc < 876 then
(if pc = 875 then some (.load 8 16) else none)
else (if pc = 876 then some (.set 23) else none)))
else (if pc < 879 then
(if pc < 878 then
(if pc = 877 then some (.get 1) else none)
else (if pc = 878 then some (.get 14) else none))
else (if pc < 880 then
(if pc = 879 then some (.bin .add) else none)
else (if pc = 880 then some (.tee 15) else none))))
else (if pc < 885 then
(if pc < 883 then
(if pc < 882 then
(if pc = 881 then some (.get 4) else none)
else (if pc = 882 then some (.load 8 24) else none))
else (if pc < 884 then
(if pc = 883 then some (.store 8 24) else none)
else (if pc = 884 then some (.get 15) else none)))
else (if pc < 887 then
(if pc < 886 then
(if pc = 885 then some (.get 23) else none)
else (if pc = 886 then some (.store 8 16) else none))
else (if pc < 888 then
(if pc = 887 then some (.get 15) else none)
else (if pc = 888 then some (.get 22) else none))))))
else (if pc < 904 then
(if pc < 896 then
(if pc < 892 then
(if pc < 890 then
(if pc = 889 then some (.store 8 8) else none)
else (if pc < 891 then
(if pc = 890 then some (.get 15) else none)
else (if pc = 891 then some (.get 21) else none)))
else (if pc < 894 then
(if pc < 893 then
(if pc = 892 then some (.store 8 0) else none)
else (if pc = 893 then some (.end) else none))
else (if pc < 895 then
(if pc = 894 then some (.get 11) else none)
else (if pc = 895 then some (.get 2) else none))))
else (if pc < 900 then
(if pc < 898 then
(if pc < 897 then
(if pc = 896 then some (.bin .lt) else none)
else (if pc = 897 then some (.brIf 0) else none))
else (if pc < 899 then
(if pc = 898 then some (.end) else none)
else (if pc = 899 then some (.end) else none)))
else (if pc < 902 then
(if pc < 901 then
(if pc = 900 then some (.get 16) else none)
else (if pc = 901 then some (.ret) else none))
else (if pc < 903 then
(if pc = 902 then some (.end) else none)
else (if pc = 903 then some (.get 15) else none)))))
else (if pc < 912 then
(if pc < 908 then
(if pc < 906 then
(if pc < 905 then
(if pc = 904 then some (.get 3) else none)
else (if pc = 905 then some (.const 66228) else none))
else (if pc < 907 then
(if pc = 906 then some (.call 2) else none)
else (if pc = 907 then some (.trap) else none)))
else (if pc < 910 then
(if pc < 909 then
(if pc = 908 then some (.end) else none)
else (if pc = 909 then some (.get 14) else none))
else (if pc < 911 then
(if pc = 910 then some (.get 10) else none)
else (if pc = 911 then some (.get 3) else none))))
else (if pc < 916 then
(if pc < 914 then
(if pc < 913 then
(if pc = 912 then some (.const 66132) else none)
else (if pc = 913 then some (.call 1) else none))
else (if pc < 915 then
(if pc = 914 then some (.trap) else none)
else (if pc = 915 then some (.end) else none)))
else (if pc < 918 then
(if pc < 917 then
(if pc = 916 then some (.get 18) else none)
else (if pc = 917 then some (.get 3) else none))
else (if pc < 919 then
(if pc = 918 then some (.const 66180) else none)
else (if pc = 919 then some (.call 2) else none)))))))
else (if pc < 951 then
(if pc < 935 then
(if pc < 927 then
(if pc < 923 then
(if pc < 921 then
(if pc = 920 then some (.trap) else none)
else (if pc < 922 then
(if pc = 921 then some (.end) else none)
else (if pc = 922 then some (.const 0) else none)))
else (if pc < 925 then
(if pc < 924 then
(if pc = 923 then some (.get 13) else none)
else (if pc = 924 then some (.get 3) else none))
else (if pc < 926 then
(if pc = 925 then some (.const 66020) else none)
else (if pc = 926 then some (.call 1) else none))))
else (if pc < 931 then
(if pc < 929 then
(if pc < 928 then
(if pc = 927 then some (.trap) else none)
else (if pc = 928 then some (.end) else none))
else (if pc < 930 then
(if pc = 929 then some (.get 15) else none)
else (if pc = 930 then some (.get 13) else none)))
else (if pc < 933 then
(if pc < 932 then
(if pc = 931 then some (.get 3) else none)
else (if pc = 932 then some (.const 66036) else none))
else (if pc < 934 then
(if pc = 933 then some (.call 1) else none)
else (if pc = 934 then some (.trap) else none)))))
else (if pc < 943 then
(if pc < 939 then
(if pc < 937 then
(if pc < 936 then
(if pc = 935 then some (.end) else none)
else (if pc = 936 then some (.const 65536) else none))
else (if pc < 938 then
(if pc = 937 then some (.const 43) else none)
else (if pc = 938 then some (.const 66148) else none)))
else (if pc < 941 then
(if pc < 940 then
(if pc = 939 then some (.call 8) else none)
else (if pc = 940 then some (.trap) else none))
else (if pc < 942 then
(if pc = 941 then some (.end) else none)
else (if pc = 942 then some (.const 0) else none))))
else (if pc < 947 then
(if pc < 945 then
(if pc < 944 then
(if pc = 943 then some (.get 4) else none)
else (if pc = 944 then some (.get 3) else none))
else (if pc < 946 then
(if pc = 945 then some (.const 66020) else none)
else (if pc = 946 then some (.call 1) else none)))
else (if pc < 949 then
(if pc < 948 then
(if pc = 947 then some (.trap) else none)
else (if pc = 948 then some (.end) else none))
else (if pc < 950 then
(if pc = 949 then some (.get 15) else none)
else (if pc = 950 then some (.get 4) else none))))))
else (if pc < 966 then
(if pc < 958 then
(if pc < 954 then
(if pc < 952 then
(if pc = 951 then some (.get 3) else none)
else (if pc < 953 then
(if pc = 952 then some (.const 66036) else none)
else (if pc = 953 then some (.call 1) else none)))
else (if pc < 956 then
(if pc < 955 then
(if pc = 954 then some (.trap) else none)
else (if pc = 955 then some (.end) else none))
else (if pc < 957 then
(if pc = 956 then some (.const 65536) else none)
else (if pc = 957 then some (.const 43) else none))))
else (if pc < 962 then
(if pc < 960 then
(if pc < 959 then
(if pc = 958 then some (.const 66148) else none)
else (if pc = 959 then some (.call 8) else none))
else (if pc < 961 then
(if pc = 960 then some (.trap) else none)
else (if pc = 961 then some (.end) else none)))
else (if pc < 964 then
(if pc < 963 then
(if pc = 962 then some (.const 0) else none)
else (if pc = 963 then some (.get 4) else none))
else (if pc < 965 then
(if pc = 964 then some (.get 3) else none)
else (if pc = 965 then some (.const 66020) else none)))))
else (if pc < 974 then
(if pc < 970 then
(if pc < 968 then
(if pc < 967 then
(if pc = 966 then some (.call 1) else none)
else (if pc = 967 then some (.trap) else none))
else (if pc < 969 then
(if pc = 968 then some (.end) else none)
else (if pc = 969 then some (.get 15) else none)))
else (if pc < 972 then
(if pc < 971 then
(if pc = 970 then some (.get 4) else none)
else (if pc = 971 then some (.get 3) else none))
else (if pc < 973 then
(if pc = 972 then some (.const 66036) else none)
else (if pc = 973 then some (.call 1) else none))))
else (if pc < 978 then
(if pc < 976 then
(if pc < 975 then
(if pc = 974 then some (.trap) else none)
else (if pc = 975 then some (.end) else none))
else (if pc < 977 then
(if pc = 976 then some (.const 65536) else none)
else (if pc = 977 then some (.const 43) else none)))
else (if pc < 980 then
(if pc < 979 then
(if pc = 978 then some (.const 66148) else none)
else (if pc = 979 then some (.call 8) else none))
else (if pc < 981 then
(if pc = 980 then some (.trap) else none)
else (if pc = 981 then some (.ret) else none)))))))))))
end Artifact
