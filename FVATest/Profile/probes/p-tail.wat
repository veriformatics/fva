(module
  (type $t (func (param i32) (result i32)))
  (table 1 funcref)
  (elem (i32.const 0) $id)
  (func $id (type $t) (local.get 0))
  (func (export "direct") (param i32) (result i32) (return_call $id (local.get 0)))
  (func (export "indirect") (param i32) (result i32)
    (return_call_indirect (type $t) (local.get 0) (i32.const 0)))
  (func (export "ref") (param i32) (result i32) (return_call_ref $t (local.get 0) (ref.func $id))))
