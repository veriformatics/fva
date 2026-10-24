import FVA.Impl.Exec.Det

/-!
# Execution and numeric helpers, pinned

Concrete cases of behavior the U3/U4 contracts specify that no other proof or official test
fixes (U12 survivors: reviewer-8 F2–F7).
-/

namespace FVA.Wasm.Exec.Pin

open FVA.Wasm.Num

/-- U3 I2: with no NaN input, the result is the positive canonical NaN. -/
theorem nanOf_default : Impl.nanOf f32fmt [] = .nan false f32fmt.canon := rfl

private def tt : TableType := { limits := { min := 0, max := none }, elem := .funcref }

/-- U4 S5 (Wasm 2.0 §4.5.3): imported table addresses precede the module's own tables. -/
theorem allocModule_tables_imports_first :
    (allocModule { tables := [{ type := tt, elem := [] }] }
      { imports := [{ module := "env", name := "t", desc := .table tt }], tables := [tt] }
      [.table 0] [] []).2.tables = [0, 1] := rfl

/-- U4 S5: active and declarative element segments initialize before data segments. -/
theorem initCode_elems_first :
    (initCode
      { mems := [{ min := 1, max := none }]
        elems := [{ type := .funcref, init := [], mode := .declarative }]
        datas := [{ init := [7], mode := .active 0 [.iconst .w32 0] }] }).head? =
      some (.elemDrop 0) := rfl

/-- U4: a reference-typed local starts as the null reference of its type. -/
theorem default_ref : (ValType.ref .funcref).default = .ref (.null .funcref) := rfl

/-- Wasm 2.0 `growmem`: growing to exactly `2^16` pages succeeds. -/
theorem grow_to_limit :
    (MemInst.grow { pages := 65535, max := none, byte := fun _ => 0 } 1).map MemInst.pages =
      some 65536 := rfl

/-- Wasm 2.0 `ref.is_null`: a null reference is null. -/
theorem isNull_null : Ref.isNull (.null .funcref) = true := rfl

/-- Wasm 2.0 `ictz`: an odd number has no trailing zero bits. -/
theorem ictz_one : ictz (1 : BitVec 32) = 0 := rfl

/-- Wasm 2.0 `growtable`: growing a table to `2^32` elements fails. -/
theorem tableGrow_limit :
    TableInst.grow { type := tt, elem := [] } (2 ^ 32) (.null .funcref) = none := rfl

end FVA.Wasm.Exec.Pin
