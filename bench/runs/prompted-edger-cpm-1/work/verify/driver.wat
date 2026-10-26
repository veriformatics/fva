(module
 (import "env" "memory" (memory 16))
 (import "artifact" "calc_cpm_raw" (func $calc (param i32 i32 i32 i32)))
 (func (export "run") (param f64 f64) (result i64)
  i32.const 131072 i32.const 131136 i32.store
  i32.const 131080 i32.const 1 i32.store
  i32.const 131084 i32.const 1 i32.store
  i32.const 131096 i32.const 1 i32.store
  i32.const 131104 i32.const 131144 i32.store
  i32.const 131112 i32.const 1 i32.store
  i32.const 131116 i32.const 1 i32.store
  i32.const 131120 i32.const 2 i32.store
  i32.const 131128 i32.const 1 i32.store
  i32.const 131136 local.get 0 f64.store
  i32.const 131144 local.get 1 f64.store
  i32.const 131072 i32.const 131104 i32.const 131136 i32.const 1 call $calc
  i32.const 131136 i64.load))
