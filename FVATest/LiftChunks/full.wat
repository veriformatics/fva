(module
  (type $t0 (func (param i32) (result i32)))
  (type $t1 (func))
  (import "env" "f" (func $imp (type $t0)))
  (table 2 funcref)
  (memory 1)
  (tag $e (param i32))
  (global $g (mut i32) (i32.const 7))
  (export "run" (func $run))
  (export "mem" (memory 0))
  (start $init)
  (elem (i32.const 0) $run $init)
  (@custom "mid" (after global) "\01\02")
  (func $run (type $t0) (local i32 i64)
    local.get 0
    call $imp
    global.get $g
    i32.add
    block (result i32)
      try_table (result i32) (catch $e 0)
        i32.const 3
        throw $e
      end
    end
    i32.add)
  (func $init (type $t1)
    i32.const 0 i32.const 0 i32.const 4 memory.init 1
    data.drop 1)
  (func $big (type $t0)
    local.get 0 i32.const 1 i32.add i32.const 2 i32.mul i32.const 3 i32.add i32.const 4 i32.mul
    i32.const 5 i32.add i32.const 6 i32.mul i32.const 7 i32.add i32.const 8 i32.mul
    i32.const 9 i32.add i32.const 10 i32.mul i32.const 11 i32.add i32.const 12 i32.mul)
  (data (i32.const 16) "abcd")
  (data "passive"))
