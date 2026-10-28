;; Instantiate the unmodified artifact using Wasmtime's --preload facility.
(module
  (import "artifact" "memory" (memory 32 32))
  (import "artifact" "LZ4_decompress_safe"
    (func $decode (param i32 i32 i32 i32) (result i32)))
  (data (i32.const 131072) "\13\41\01\00\50\42\43\44\45\46")
  (data (i32.const 131088) "\13\41\00\00\50\42\43\44\45\46")
  (data (i32.const 131104) "\13\41\02\00\50\42\43\44\45\46")
  (data (i32.const 131120) "\00")
  (func $equal (param $x i32) (param $y i32)
    local.get $x local.get $y i32.ne
    if unreachable end)
  (func (export "check") (result i32)
    i32.const 131072 i32.const 262144 i32.const 10 i32.const 13
    call $decode i32.const 13 call $equal
    i32.const 262144 i32.load i32.const 0x41414141 call $equal
    i32.const 262148 i32.load i32.const 0x41414141 call $equal
    i32.const 262152 i32.load i32.const 0x45444342 call $equal
    i32.const 262156 i32.load8_u i32.const 70 call $equal
    i32.const 131088 i32.const 262144 i32.const 10 i32.const 13
    call $decode i32.const 13 call $equal
    i32.const 262144 i32.load i32.const 65 call $equal
    i32.const 262148 i32.load i32.const 0 call $equal
    i32.const 262152 i32.load i32.const 0x45444342 call $equal
    i32.const 262156 i32.load8_u i32.const 70 call $equal
    i32.const 131104 i32.const 262144 i32.const 10 i32.const 13
    call $decode i32.const 0 i32.lt_s i32.const 1 call $equal
    i32.const 131072 i32.const 262144 i32.const 10 i32.const 12
    call $decode i32.const 0 i32.lt_s i32.const 1 call $equal
    i32.const 131120 i32.const 262144 i32.const 1 i32.const 0
    call $decode i32.const 0 call $equal
    i32.const 1)
)
